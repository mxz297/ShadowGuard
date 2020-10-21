
#include <algorithm>
#include <iostream>
#include <vector>

#include "BPatch.h"
#include "BPatch_basicBlock.h"
#include "BPatch_edge.h"
#include "BPatch_flowGraph.h"
#include "BPatch_function.h"
#include "BPatch_object.h"
#include "BPatch_point.h"

#include "InstSpec.h"
#include "PatchMgr.h"
#include "PatchModifier.h"
#include "Point.h"


#include "gflags/gflags.h"
#include "glog/logging.h"

#include "parse.h"
#include "pass_manager.h"
#include "passes.h"
#include "utils.h"

#include "Module.h"
#include "Symbol.h"

#include "snippet.h"

using namespace Dyninst;
using namespace Dyninst::PatchAPI;

DECLARE_bool(libs);
DECLARE_bool(vv);

DECLARE_string(output);
DECLARE_string(shadow_stack);
DECLARE_string(threat_model);
DECLARE_string(stats);
DECLARE_string(skip_list);

DECLARE_bool(disable_reg_frame);
DECLARE_bool(disable_reg_save_opt);
DECLARE_bool(disable_inline);
DECLARE_bool(disable_sfe);

// Implemented in safe_path_elision.cc
extern
bool DoInstrumentationLowering(BPatch_function* function, FuncSummary* summary,
                               const litecfi::Parser& parser,
                               PatchMgr::Ptr patcher);
extern
bool CheckFastPathFunction(BPatch_basicBlock*& entry,
                           vector<BPatch_basicBlock*>& exits,
                           BPatch_function* f);


// Implemented in cfp_inline.cc
extern
bool ControlFlowPathInlining(BPatch_function* function, FuncSummary* summary,
                             const litecfi::Parser& parser,
                             PatchMgr::Ptr patcher);

// Thread local shadow stack initialization function name.
static constexpr char kShadowStackInitFn[] = "litecfi_init_mem_region";
// Init function which needs to be instrumented with a call the thread local
// shadow stack initialzation function above.
static constexpr char kInitFn[] = "_start";

// Trampoline specifications.
static InstSpec is_init;
static InstSpec is_empty;
static std::set<Address> skip_addrs;

CFGMaker* cfgMaker;
static int total_func = 0;
static int func_with_indirect_or_plt_call = 0;
static int func_with_indirect_call = 0;
static int func_with_plt_call = 0;
static int memory_writes = 0;
static int stack_writes = 0;
static int heap_writes = 0;
static int global_writes = 0;
static int arg_writes = 0;
static int heap_or_arg_writes = 0;
int total_dead_reg_site = 0;
int no_dead_reg_site = 0;
int lowering_dead_reg_site = 0;
int lowering_no_dead_reg_entry_site = 0;
int lowering_no_dead_reg_exit_site = 0;

struct InstrumentationResult {
  std::vector<std::string> safe_fns;
  std::vector<std::string> lowered_fns;
  std::vector<std::string> reg_stack_fns;
};

bool IsNonreturningCall(Point* point) {
  PatchBlock* exitBlock = point->block();
  assert(exitBlock);
  bool call = false;
  bool callFT = false;
  for (auto e : exitBlock->targets()) {
    if (e->type() == CALL)
      call = true;
    if (e->type() == CALL_FT)
      callFT = true;
  }
  return (call && !callFT);
}

void InsertSnippet(BPatch_function* function, Point::Type location,
                   Snippet::Ptr snippet, PatchMgr::Ptr patcher) {
  std::vector<Point*> points;
  patcher->findPoints(Scope(Dyninst::PatchAPI::convert(function)), location,
                      back_inserter(points));

  for (auto it = points.begin(); it != points.end(); ++it) {
    Point* point = *it;
    // Do not instrument function exits that are calls to non-returning
    // functions because the stack frame may still not be tear down, causing the
    // instrumentation to get wrong return address.
    if (location == Point::FuncExit && IsNonreturningCall(point))
      continue;
    point->pushBack(snippet);
  }
}


bool DoStackOpsUsingRegisters(BPatch_function* function, FuncSummary* summary,
                              const litecfi::Parser& parser,
                              PatchMgr::Ptr patcher) {
  if (FLAGS_disable_reg_frame) return false;
  if (summary != nullptr && summary->shouldUseRegisterFrame()) {
    fprintf(stdout, "[Register Stack] Function : %s\n",
            Dyninst::PatchAPI::convert(function)->name().c_str());
    Snippet::Ptr stack_push =
        RegisterPushSnippet::create(new RegisterPushSnippet(summary));
    InsertSnippet(function, Point::FuncEntry, stack_push, patcher);

    Snippet::Ptr stack_pop =
        RegisterPopSnippet::create(new RegisterPopSnippet(summary));
    InsertSnippet(function, Point::FuncExit, stack_pop, patcher);

    BPatch_nullExpr nopSnippet;
    vector<BPatch_point*> points;
    function->getEntryPoints(points);
    BPatch_binaryEdit* binary_edit = ((BPatch_binaryEdit*)parser.app);

    binary_edit->insertSnippet(nopSnippet, points, BPatch_callBefore,
                               BPatch_lastSnippet, &is_empty);

    points.clear();
    function->getExitPoints(points);
    binary_edit->insertSnippet(nopSnippet, points, BPatch_callAfter,
                               BPatch_lastSnippet, &is_empty);
    return true;
  }
  return false;
}



void AddInlineHint(BPatch_function* function, const litecfi::Parser& parser, FuncSummary * summary) {
  if (FLAGS_disable_inline) return;
  // Do no attempt to inline functions that we do not need to instrument
  if (summary != nullptr && summary->safe) return;
  Address entry = (Address)(function->getBaseAddr());
  parser.parser->addInliningEntry(entry);
}

bool Skippable(BPatch_function* function, FuncSummary* summary) {
  if (FLAGS_disable_sfe) return false;
  if (summary != nullptr && summary->safe) {
    StdOut(Color::RED, FLAGS_vv)
        << "      Skipping function : " << function->getName() << Endl;
    return true;
  }

  Address addr = (Address)(function->getBaseAddr());

  if (skip_addrs.find(addr) != skip_addrs.end()) {
    StdOut(Color::RED, FLAGS_vv)
        << "      Skipping function (user's skip list): " << function->getName()
        << Endl;

    return true;
  }
  return false;
}

bool MoveInstrumentation(BPatch_point*& p, FuncSummary* s) {
  if (FLAGS_disable_reg_save_opt) return false;
  if (s == nullptr) return false;
  ++total_dead_reg_site;
  if (p->getPointType() == BPatch_locEntry) {
    BPatch_function* f = p->getFunction();
    BPatch_flowGraph* cfg = f->getCFG();

    // Should have only one function entry block.
    std::vector<BPatch_basicBlock*> eb;
    cfg->getEntryBasicBlock(eb);
    if (eb.size() != 1) {
      ++no_dead_reg_site;
      return false;
    }

    // If the function entry block has intra-procedural
    // incoming edges, then we have to instrument at function entry.
    // Otherwise, the stack push op will be executed in a loop
    BPatch_basicBlock* func_entry = eb[0];
    std::vector<BPatch_edge*> edges;
    func_entry->getIncomingEdges(edges);
    if (edges.size() > 0) {
      ++no_dead_reg_site;
      return false;
    }
    MoveInstData* mid =
        s->getMoveInstDataAtEntry(func_entry->getStartAddress());
    if (mid == nullptr) {
      ++no_dead_reg_site;
      return false;
    }
    p = func_entry->findPoint(mid->newInstAddress);
  } else if (p->getPointType() == BPatch_locBasicBlockEntry) {
    BPatch_basicBlock* b = p->getBlock();
    MoveInstData* mid = s->getMoveInstDataAtEntry(b->getStartAddress());
    if (mid == nullptr) {
      ++no_dead_reg_site;
      return false;
    }
    p = b->findPoint(mid->newInstAddress);
  } else if (p->getPointType() == BPatch_locExit ||
             p->getPointType() == BPatch_locBasicBlockExit) {
    BPatch_basicBlock* b = p->getBlock();
    MoveInstData* mid = s->getMoveInstDataAtExit(b->getStartAddress());
    if (mid == nullptr) {
      ++no_dead_reg_site;
      return false;
    }
    p = b->findPoint(mid->newInstAddress);
  } else {
    // Cannot move instrumentation if instrumenting at an edge
    ++no_dead_reg_site;
    return false;
  }
  return true;
}

void CountMemoryWrites(FuncSummary* s) {
  if (s == nullptr) return;
  for (auto const &it : s->all_writes) {
    auto const& w = it.second;
    memory_writes += 1;
    int type_count = 0;
    type_count += (int)(w->stack);
    type_count += (int)(w->global);
    type_count += (int)(w->heap);
    type_count += (int)(w->arg);
    type_count += (int)(w->heap_or_arg);
    if (type_count >= 2) {
        fprintf(stderr, "write at %lx classified more than one type\n", w->addr);
        fprintf(stderr, "\tstack: %d, global: %d, heap: %d, arg: %d, heap_or_arg: %d\n", w->stack, w->global, w->heap, w->arg, w->heap_or_arg);
        assert(0);
    }
    if (w->stack) stack_writes += 1;
    if (w->global) global_writes += 1;
    if (w->heap) {
        heap_writes += 1;
    }
    if (w->arg) arg_writes += 1;
    if (w->heap_or_arg) heap_or_arg_writes += 1;
  }
}

void InstrumentFunction(BPatch_function* function,
                        const litecfi::Parser& parser, PatchMgr::Ptr patcher,
                        const std::map<uint64_t, FuncSummary*>& analyses,
                        InstrumentationResult* res) {
  function->setLayoutOrder((uint64_t)(function->getBaseAddr()));
  total_func++;
  std::string fn_name = Dyninst::PatchAPI::convert(function)->name();
  StdOut(Color::YELLOW, FLAGS_vv) << "     Function : " << fn_name << Endl;

  BPatch_binaryEdit* binary_edit = ((BPatch_binaryEdit*)parser.app);
  BPatch_nullExpr nopSnippet;
  vector<BPatch_point*> points;
  FuncSummary* summary = nullptr;

  if (FLAGS_shadow_stack == "light") {
    auto it = analyses.find(static_cast<uint64_t>(
        reinterpret_cast<uintptr_t>(function->getBaseAddr())));
    if (it != analyses.end())
      summary = (*it).second;
    if (summary != nullptr) {
      if (summary->has_unknown_cf || !summary->plt_calls.empty())
        func_with_indirect_or_plt_call++;
      if (summary->has_unknown_cf)
        func_with_indirect_call++;
      if (!summary->plt_calls.empty())
        func_with_plt_call++;
    }

    CountMemoryWrites(summary);

    // Check if this function is safe to skip and do so if it is.
    if (Skippable(function, summary)) {
      function->relocateFunction();
      res->safe_fns.push_back(fn_name);
      return;
    }

    // Add inlining hint so that writeFile may inline small leaf functions.
    AddInlineHint(function, parser, summary);

    // If possible check and lower the instrumentation to within non frequently
    // executed unsafe control flow paths.
    if (DoInstrumentationLowering(function, summary, parser, patcher)) {
      res->lowered_fns.push_back(fn_name);
      StdOut(Color::RED, FLAGS_vv)
          << "      Optimized instrumentation lowering for function at 0x"
          << std::hex << (uint64_t)function->getBaseAddr() << Endl;

      return;
    }

    // For leaf functions we may be able to carry out stack operations using
    // unused registers.
    if (DoStackOpsUsingRegisters(function, summary, parser, patcher)) {
      res->reg_stack_fns.push_back(fn_name);
      return;
    }

    // Apply fast path optimization if applicable.
    BPatch_basicBlock* condNotTakenEntry = NULL;
    vector<BPatch_basicBlock*> condNotTakenExits;
    if (summary != nullptr && CheckFastPathFunction(condNotTakenEntry, condNotTakenExits, function)) {
      res->lowered_fns.push_back(fn_name);
      StdOut(Color::RED, FLAGS_vv)
          << "      Optimized fast path instrumentation for function at 0x"
          << std::hex << (uint64_t)function->getBaseAddr() << Endl;
      /* If the function has the following shape:
       * entry:
       *    code that does not writes memory
       *    jz A   (or other conditional jump)
       *    some complicated code
       * A: ret
       *
       * Then we do not need to instrument the fast path: entry -> ret.
       * We can instrument the entry and exit of the "some complicated code",
       * which is the slow path.
       */

      // Instrument slow paths entry with stack push operation
      // and nop snippet, which enables instrumentation frame spec.
      //
      // Also attempt to move instrumentation to utilize existing push & pop
      BPatch_point* push_point = condNotTakenEntry->findEntryPoint();
      bool moveInst = MoveInstrumentation(push_point, summary);
      Snippet::Ptr stack_push =
          StackPushSnippet::create(new StackPushSnippet(summary, moveInst));
      PatchAPI::convert(push_point, BPatch_callBefore)->pushBack(stack_push);
      points.push_back(push_point);
      binary_edit->insertSnippet(nopSnippet, points, BPatch_callBefore,
                                 BPatch_lastSnippet, &is_empty);

      // Instrument slow paths exits with stack pop operations
      // and nop snippet, which enables instrumentation frame spec.
      points.clear();
      std::vector<BPatch_point*> insnPoints;
      for (auto b : condNotTakenExits) {
        BPatch_point* pop_point = b->findExitPoint();
        bool moveInst = MoveInstrumentation(pop_point, summary);
        Snippet::Ptr stack_pop =
            StackPopSnippet::create(new StackPopSnippet(summary, moveInst));
        if (pop_point->getPointType() == BPatch_locInstruction) {
          PatchAPI::convert(pop_point, BPatch_callBefore)->pushBack(stack_pop);
          insnPoints.push_back(pop_point);
        } else {
          PatchAPI::convert(pop_point, BPatch_callAfter)->pushBack(stack_pop);
          points.push_back(pop_point);
        }
      }
      binary_edit->insertSnippet(nopSnippet, insnPoints, BPatch_callBefore,
                                 BPatch_lastSnippet, &is_empty);
      binary_edit->insertSnippet(nopSnippet, points, BPatch_callAfter,
                                 BPatch_lastSnippet, &is_empty);
      return;
    } else {
      // Attempt to move instrumentation to utilize
      // existing push & pop
      std::vector<BPatch_point*> entryPoints;
      function->getEntryPoints(entryPoints);
      for (auto& p : entryPoints) {
        bool moveInst = MoveInstrumentation(p, summary);
        Snippet::Ptr stack_push =
            StackPushSnippet::create(new StackPushSnippet(summary, moveInst));
        PatchAPI::convert(p, BPatch_callBefore)->pushBack(stack_push);
      }
      binary_edit->insertSnippet(nopSnippet, entryPoints, BPatch_callBefore,
                                 BPatch_lastSnippet, &is_empty);

      std::vector<BPatch_point*> exitPoints;
      function->getExitPoints(exitPoints);

      std::vector<BPatch_point*> beforePoints;
      std::vector<BPatch_point*> afterPoints;
      for (auto& p : exitPoints) {
        if (IsNonreturningCall(PatchAPI::convert(p, BPatch_callAfter)))
          continue;
        bool moveInst = MoveInstrumentation(p, summary);
        Snippet::Ptr stack_pop =
            StackPopSnippet::create(new StackPopSnippet(summary, moveInst));
        if (p->getPointType() == BPatch_locInstruction) {
          PatchAPI::convert(p, BPatch_callBefore)->pushBack(stack_pop);
          beforePoints.push_back(p);
        } else {
          PatchAPI::convert(p, BPatch_callAfter)->pushBack(stack_pop);
          afterPoints.push_back(p);
        }
      }
      binary_edit->insertSnippet(nopSnippet, beforePoints, BPatch_callBefore,
                                 BPatch_lastSnippet, &is_empty);
      binary_edit->insertSnippet(nopSnippet, afterPoints, BPatch_callAfter,
                                 BPatch_lastSnippet, &is_empty);
      if (ControlFlowPathInlining(function, summary, parser, patcher)) {
      }
      return;
    }
  }

  // Either we are in 'full' instrumentation mode or in 'light' mode but none of
  // the optimizations worked out. Carry out regular entry-exit shadow stack
  // instrumentation.
  Snippet::Ptr stack_push =
      StackPushSnippet::create(new StackPushSnippet(summary, false));
  InsertSnippet(function, Point::FuncEntry, stack_push, patcher);

  Snippet::Ptr stack_pop =
      StackPopSnippet::create(new StackPopSnippet(summary, false));
  InsertSnippet(function, Point::FuncExit, stack_pop, patcher);

  function->getEntryPoints(points);
  binary_edit->insertSnippet(nopSnippet, points, BPatch_callBefore,
                             BPatch_lastSnippet, &is_empty);

  points.clear();
  function->getExitPoints(points);
  binary_edit->insertSnippet(nopSnippet, points, BPatch_callAfter,
                             BPatch_lastSnippet, &is_empty);
}

BPatch_function* FindFunctionByName(BPatch_image* image, std::string name) {
  BPatch_Vector<BPatch_function*> funcs;
  if (image->findFunction(name.c_str(), funcs,
                          /* showError */ true,
                          /* regex_case_sensitive */ true,
                          /* incUninstrumentable */ true) == nullptr ||
      !funcs.size() || funcs[0] == nullptr) {
    return nullptr;
  }
  return funcs[0];
}

void InstrumentInitFunction(BPatch_function* function,
                            const litecfi::Parser& parser) {
  BPatch_binaryEdit* binary_edit = ((BPatch_binaryEdit*)parser.app);
  BPatch_Vector<BPatch_snippet*> args;

  auto stack_init_fn = FindFunctionByName(parser.image, kShadowStackInitFn);

  BPatch_funcCallExpr stack_init(*stack_init_fn, args);
  std::vector<BPatch_point*>* entries = function->findPoint(BPatch_entry);
  BPatchSnippetHandle* handle = nullptr;
  handle = binary_edit->insertSnippet(stack_init, *entries, BPatch_callBefore,
                                      BPatch_lastSnippet, &is_init);
  DCHECK(handle != nullptr)
      << "Failed to instrument init function for stack initialization.";
}

void InstrumentModule(BPatch_module* module, const litecfi::Parser& parser,
                      PatchMgr::Ptr patcher,
                      const std::map<uint64_t, FuncSummary*>& analyses,
                      InstrumentationResult* res) {
  std::vector<BPatch_function*>* functions = module->getProcedures();

  for (auto it = functions->begin(); it != functions->end(); it++) {
    BPatch_function* function = *it;

    ParseAPI::Function* f = ParseAPI::convert(function);
    if (f->retstatus() == ParseAPI::NORETURN)
      continue;

    // We should only instrument functions in .text.
    ParseAPI::CodeRegion* codereg = f->region();
    ParseAPI::SymtabCodeRegion* symRegion =
        dynamic_cast<ParseAPI::SymtabCodeRegion*>(codereg);
    assert(symRegion);
    SymtabAPI::Region* symR = symRegion->symRegion();
    if (symR->getRegionName() != ".text")
      continue;

    InstrumentFunction(function, parser, patcher, analyses, res);
  }
}

void InstrumentCodeObject(BPatch_object* object, const litecfi::Parser& parser,
                          PatchMgr::Ptr patcher, InstrumentationResult* res) {
  if (!IsSharedLibrary(object)) {
    StdOut(Color::GREEN, FLAGS_vv) << "\n  >> Instrumenting main application "
                                   << object->pathName() << Endl;
  } else {
    StdOut(Color::GREEN, FLAGS_vv)
        << "\n    Instrumenting " << object->pathName() << Endl;
  }

  if (FLAGS_threat_model == "trust_system" && IsSystemCode(object)) {
    return;
  }

  std::vector<BPatch_module*> modules;
  object->modules(modules);

  std::map<uint64_t, FuncSummary*> analyses;
  // Do the static analysis on this code and obtain skippable functions.
  if (FLAGS_shadow_stack == "light") {
    CodeObject* co = Dyninst::ParseAPI::convert(object);
    co->parse();
    co->adjustJumpTableRange();

    PassManager* pm = new PassManager;
    pm->AddPass(new CallGraphAnalysis())
        ->AddPass(new LargeFunctionFilter())
        ->AddPass(new StackHeightAnalysis())
        ->AddPass(new CFGAnalysis())
//        ->AddPass(new HeapWriteAnalysis())
        ->AddPass(new InterProceduralMemoryAnalysis())
        ->AddPass(new UnsafeCallBlockAnalysis())
        ->AddPass(new SafePathsCounting())
        ->AddPass(new DeadRegisterAnalysis())
        ->AddPass(new UnusedRegisterAnalysis())
        ->AddPass(new BlockDeadRegisterAnalysis());
    std::set<FuncSummary*> summaries = pm->Run(co);

    for (auto f : summaries) {
      analyses[f->func->addr()] = f;
    }
  }

  for (auto it = modules.begin(); it != modules.end(); it++) {
    char modname[2048];
    BPatch_module* module = *it;
    module->getName(modname, 2048);

    InstrumentModule(module, parser, patcher, analyses, res);
  }
}

void SetupInstrumentationSpec() {
  // Suppose we instrument a call to stack init at entry of A;
  // If A does not use r11, we dont need to save r11 (_start does not).
  is_init.trampGuard = false;
  is_init.redZone = false;
  is_init.saveRegs.push_back(x86_64::rax);
  is_init.saveRegs.push_back(x86_64::rdx);

  is_empty.trampGuard = false;
  is_empty.redZone = false;
}

void Instrument(std::string binary, const litecfi::Parser& parser) {
  StdOut(Color::BLUE, FLAGS_vv) << "\n\nInstrumentation Pass" << Endl;
  StdOut(Color::BLUE, FLAGS_vv) << "====================" << Endl;

  cfgMaker = parser.parser->getCFGMaker();

  StdOut(Color::BLUE) << "+ Instrumenting the binary..." << Endl;

  if (FLAGS_skip_list != "") {
    std::ifstream infile(FLAGS_skip_list, std::fstream::in);
    Address addr;
    while (infile >> std::hex >> addr)
      skip_addrs.insert(addr);
  }

  std::vector<BPatch_object*> objects;
  parser.image->getObjects(objects);

  PatchMgr::Ptr patcher = Dyninst::PatchAPI::convert(parser.app);
  BPatch_binaryEdit* binary_edit = ((BPatch_binaryEdit*)parser.app);

  SetupInstrumentationSpec();

  InstrumentationResult* res = new InstrumentationResult;

  for (auto it = objects.begin(); it != objects.end(); it++) {
    BPatch_object* object = *it;

    // Skip other shared libraries for now.
    if (!FLAGS_libs && IsSharedLibrary(object)) {
      continue;
    }

    InstrumentCodeObject(object, parser, patcher, res);
  }

  if (FLAGS_output.empty()) {
    binary_edit->writeFile((binary + "_cfi").c_str());
  } else {
    binary_edit->writeFile(FLAGS_output.c_str());
  }

  StdOut(Color::RED) << "Safe functions : " << std::dec << res->safe_fns.size() << "(" << res->safe_fns.size() * 100.0 / total_func << "%)"
                     << "\n  ";
  /*
  for (auto it : res->safe_fns) {
    StdOut(Color::BLUE) << it << " ";
  }
  */
  StdOut(Color::BLUE) << Endl << Endl;

  StdOut(Color::RED) << "Register stack functions : "
                     << res->reg_stack_fns.size() << "(" << res->reg_stack_fns.size() * 100.0 / total_func << "%)"<< "\n  ";
  /*
  for (auto it : res->reg_stack_fns) {
    StdOut(Color::BLUE) << it << " ";
  }
  */
  StdOut(Color::BLUE) << Endl << Endl;
  StdOut(Color::RED) << "Lowering stack functions : " << res->lowered_fns.size() << "(" << res->lowered_fns.size() * 100.0 / total_func << "%)"
                     << "\n  ";
  /*
  for (auto it : res->lowered_fns) {
    StdOut(Color::BLUE) << it << " ";
  }
  */
  StdOut(Color::BLUE) << Endl;
  StdOut(Color::RED) << "Functions with indirect call or plt calls : "
                     << func_with_indirect_or_plt_call
                     << Endl;
  StdOut(Color::RED) << "Functions with indirect call: "
                     << func_with_indirect_call 
                     << Endl;
  StdOut(Color::RED) << "Functions with plt calls : " << func_with_plt_call
                     << Endl;
  StdOut(Color::RED) << "Total functions : " << total_func << Endl;

  StdOut(Color::RED) << "Total memory writes : " << memory_writes << Endl;
  StdOut(Color::RED) << "\tStack writes : " << stack_writes << "(" << stack_writes * 100.0 / memory_writes << "%)" << Endl;
  StdOut(Color::RED) << "\tGlobal writes : " << global_writes <<  "(" << global_writes * 100.0 / memory_writes << "%)" << Endl;
  StdOut(Color::RED) << "\tHeap writes : " << heap_writes << "(" << heap_writes * 100.0 / memory_writes << "%)" << Endl;
  StdOut(Color::RED) << "\tArg writes : " << arg_writes << "(" << arg_writes * 100.0 / memory_writes << "%)" <<  Endl;
  StdOut(Color::RED) << "\tHeap_or_arg writes : " << heap_or_arg_writes << "(" << heap_or_arg_writes * 100.0 / memory_writes << "%)" <<  Endl;

  int unknown = memory_writes;
  unknown -= stack_writes;
  unknown -= global_writes;
  unknown -= heap_writes;
  unknown -= arg_writes;
  unknown -= heap_or_arg_writes;
  StdOut(Color::RED) << "\tUnknown writes : " << unknown << "(" << unknown * 100.0 / memory_writes << "%)" <<  Endl;
  StdOut(Color::RED) << "Dead register optimization : " << no_dead_reg_site << "/" << total_dead_reg_site << Endl;
  StdOut(Color::RED) << "Lowering dead register optimization : " << lowering_no_dead_reg_entry_site << "/" << lowering_no_dead_reg_exit_site << "/" << lowering_dead_reg_site << Endl;

}
