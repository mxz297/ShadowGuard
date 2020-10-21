#include "BPatch_function.h"
#include "BPatch_basicBlock.h"
#include "BPatch_edge.h"
#include "BPatch_flowGraph.h"

#include "PatchCFG.h"
#include "PatchMgr.h"
#include "Point.h"
#include "PatchModifier.h"

#include "gflags/gflags.h"
#include "pass_manager.h"
#include "parse.h"
#include "utils.h"
#include "snippet.h"

using namespace Dyninst;
using namespace Dyninst::PatchAPI;

extern CFGMaker* cfgMaker;
extern int lowering_dead_reg_site;
extern int lowering_no_dead_reg_entry_site;
extern int lowering_no_dead_reg_exit_site;

extern bool IsNonreturningCall(Point* point);

DECLARE_bool(disable_lowering);
DECLARE_bool(disable_reg_frame);
DECLARE_bool(disable_reg_save_opt);

static bool skipPatchEdges(
  PatchEdge* e
) {
  if (e->sinkEdge() || e->interproc())
    return true;
  if (e->type() == ParseAPI::CATCH)
    return true;
  return false;
}

static void CloneFunctionCFG(
  PatchFunction* f,
  PatchMgr::Ptr patcher,
  std::map<PatchBlock*, PatchBlock*>& cloneBlockMap
) {
  // Clone all blocks
  std::vector<PatchBlock*> newBlocks;
  for (auto b : f->blocks()) {
    PatchBlock* cloneB = cfgMaker->cloneBlock(b, b->object());
    cloneBlockMap[b] = cloneB;
    newBlocks.push_back(cloneB);
  }
  for (auto b : newBlocks) {
    PatchModifier::addBlockToFunction(f, b);
  }

  // The edges of the cloned blocks are still from/to original blocks
  // Now we redirect all edges
  for (auto b : newBlocks) {
    for (auto e : b->targets()) {
      if (skipPatchEdges(e))
        continue;
      PatchBlock* newTarget = cloneBlockMap[e->trg()];
      assert(PatchModifier::redirect(e, newTarget));
    }
  }
}

static void RedirectTransitionEdges(
  PatchBlock* cur,
  FuncSummary* summary,
  std::set<PatchEdge*>& redirect,
  std::set<PatchEdge*>& visited
) {
  for (auto e : cur->targets()) {
    if (skipPatchEdges(e))
      continue;
    if (visited.find(e) != visited.end())
      continue;
    visited.insert(e);
    PatchBlock* target = e->trg();
    bool targetHasIndJump = false;
    for (auto te : target->targets()) {
      if (skipPatchEdges(te))
        continue;
      if (te->type() == ParseAPI::INDIRECT) {
        targetHasIndJump = true;
        break;
      }
    }
    if (summary->unsafe_blocks.find(target->block()) !=
        summary->unsafe_blocks.end() ||
        targetHasIndJump) {
      redirect.insert(e);
    } else {
      RedirectTransitionEdges(target, summary, redirect, visited);
    }
  }
}

static void GetReachableBlocks(
  PatchBlock* b,
  std::set<PatchBlock*>& visited
) {
  if (visited.find(b) != visited.end())
    return;
  visited.insert(b);
  for (auto e : b->targets()) {
    if (e->interproc())
      continue;
    if (e->sinkEdge())
      continue;
    if (e->type() == ParseAPI::RET || e->type() == ParseAPI::CATCH)
      continue;
    GetReachableBlocks(e->trg(), visited);
  }
}

static void CoalesceEdgeInstrumentation(
  PatchFunction* f,
  std::set<PatchEdge*>& redirect,
  std::set<PatchBlock*>& instBlocks
) {
  std::set<PatchBlock*> reachableBlocks;
  GetReachableBlocks(f->entry(), reachableBlocks);
  for (auto b : reachableBlocks) {
    if (!b->isClone())
      continue;
    int instEdges = 0;
    int notInstEdges = 0;
    bool hasCatchEdge = false;
    for (auto e : b->sources()) {
      if (redirect.find(e) != redirect.end()) {
        instEdges += 1;
        continue;
      }
      if (e->type() == ParseAPI::CATCH) {
        hasCatchEdge = true;
        continue;
      }
      if (reachableBlocks.find(e->src()) != reachableBlocks.end()) {
        notInstEdges += 1;
      }
    }
    if (!hasCatchEdge && instEdges > 0 && notInstEdges == 0) {
      instBlocks.insert(b);
      for (auto e : b->sources())
        redirect.erase(e);
    }
  }
}

bool DoInstrumentationLowering(
  BPatch_function* function,
  FuncSummary* summary,
  const litecfi::Parser& parser,
  PatchMgr::Ptr patcher
) {
  if (FLAGS_disable_lowering) return false;
  if (!summary || !summary->lowerInstrumentation()) {
    return false;
  }
  if (summary->has_indirect_cf) return false;
  PatchFunction* f = PatchAPI::convert(function);
  std::set<PatchEdge*> visited;
  std::set<PatchEdge*> redirect;
  RedirectTransitionEdges(f->entry(), summary, redirect, visited);

  for (auto e : redirect)
    if (summary->blockEndSPHeight.find(e->src()->start()) ==
        summary->blockEndSPHeight.end())
      return false;

  bool useRegisterFrame = summary->shouldUseRegisterFrame();
  if (FLAGS_disable_reg_frame) useRegisterFrame = false;
  if (!useRegisterFrame && summary->redZoneAccess.size() > 0) {
    for (auto e : redirect) {
      MoveInstData* mid =
          summary->getMoveInstDataFixedAtEntry(e->trg()->start());
      if (mid == nullptr)
        return false;
      if (mid->saveCount < 2)
        return false;
    }
  }

  assert(parser.parser->markPatchFunctionEntryInstrumented(f));

  std::map<PatchBlock*, PatchBlock*> cloneBlockMap;
  CloneFunctionCFG(f, patcher, cloneBlockMap);
  for (auto e : redirect) {
    assert(PatchModifier::redirect(e, cloneBlockMap[e->trg()]));
  }

  std::set<PatchBlock*> instBlocks;
  CoalesceEdgeInstrumentation(f, redirect, instBlocks);

  // Insert stack push operations at edges
  for (auto e : redirect) {
    // We get the stack height at block exit
    assert(summary->blockEndSPHeight.find(e->src()->start()) !=
           summary->blockEndSPHeight.end());
    int height = summary->blockEndSPHeight[e->src()->start()];
    MoveInstData* mid = summary->getMoveInstDataFixedAtEntry(e->trg()->start());
    if (FLAGS_disable_reg_save_opt) mid = nullptr;
    Snippet::Ptr stack_push;
    if (useRegisterFrame) {
      stack_push =
          RegisterPushSnippet::create(new RegisterPushSnippet(summary, height));
    } else if (mid == nullptr) {
      lowering_dead_reg_site += 1;
      lowering_no_dead_reg_entry_site += 1;
      stack_push = StackPushSnippet::create(
          new StackPushSnippet(summary, false, height));
    } else {
      lowering_dead_reg_site += 1;
      stack_push = StackPushSnippet::create(
          new StackPushSnippet(summary, false, height, true));
    }

    Point* p = patcher->findPoint(PatchAPI::Location::EdgeInstance(f, e),
                                  Point::EdgeDuring);
    assert(p);
    p->pushBack(stack_push);
  }

  // Insert stack push operations at blocks whose
  // incoming edge instrumentations are coalesced
  for (auto b : instBlocks) {
    assert(summary->blockEntrySPHeight.find(b->start()) !=
           summary->blockEntrySPHeight.end());
    int height = summary->blockEntrySPHeight[b->start()];
    MoveInstData* mid = summary->getMoveInstDataAtEntry(b->start());
    if (FLAGS_disable_reg_save_opt) mid = nullptr;
    Snippet::Ptr stack_push;
    Point* p = patcher->findPoint(PatchAPI::Location::BlockInstance(f, b),
                                  Point::BlockEntry);
    if (useRegisterFrame) {
      stack_push =
          RegisterPushSnippet::create(new RegisterPushSnippet(summary, height));
    } else if (mid == nullptr) {
      lowering_dead_reg_site += 1;
      lowering_no_dead_reg_entry_site += 1;
      stack_push = StackPushSnippet::create(
          new StackPushSnippet(summary, false, height));
    } else {
      lowering_dead_reg_site += 1;
      p = patcher->findPoint(
          PatchAPI::Location::InstructionInstance(f, b, mid->newInstAddress),
          Point::PreInsn);
      assert(p);
      stack_push =
          StackPushSnippet::create(new StackPushSnippet(summary, true, height));
    }
    assert(p);
    p->pushBack(stack_push);
  }

  // Insert stack pop operations
  for (auto b : f->exitBlocks()) {
    PatchBlock* cloneB = cloneBlockMap[b];
    Point* p = patcher->findPoint(PatchAPI::Location::BlockInstance(f, cloneB),
                                  Point::BlockExit);
    assert(p);
    if (IsNonreturningCall(p))
      continue;

    MoveInstData* mid = summary->getMoveInstDataAtExit(b->start());
    if (FLAGS_disable_reg_save_opt) mid = nullptr;

    Snippet::Ptr stack_pop;
    if (useRegisterFrame) {
      stack_pop = RegisterPopSnippet::create(new RegisterPopSnippet(summary));
    } else if (mid == nullptr) {
      lowering_dead_reg_site += 1;
      lowering_no_dead_reg_exit_site += 1;
      stack_pop = StackPopSnippet::create(new StackPopSnippet(summary, false));
    } else {
      lowering_dead_reg_site += 1;
      p = patcher->findPoint(PatchAPI::Location::InstructionInstance(
                                 f, cloneB, mid->newInstAddress),
                             Point::PreInsn);
      assert(p);
      stack_pop = StackPopSnippet::create(new StackPopSnippet(summary, true));
    }
    p->pushBack(stack_pop);
    assert(parser.parser->markPatchBlockInstrumented(cloneB));
  }

  f->setContainsClonedBlocks(true);
  return true;
}

bool CheckFastPathFunction(
  BPatch_basicBlock*& entry,
  vector<BPatch_basicBlock*>& exits,
  BPatch_function* f
) {
  if (FLAGS_disable_lowering) return false;
  BPatch_flowGraph* cfg = f->getCFG();

  // Should have only one function entry block.
  std::vector<BPatch_basicBlock*> eb;
  cfg->getEntryBasicBlock(eb);
  if (eb.size() != 1)
    return false;
  BPatch_basicBlock* func_entry = eb[0];

  // The function entry block should not contain memory writes.
  std::vector<Dyninst::InstructionAPI::Instruction> insns;
  func_entry->getInstructions(insns);
  for (auto i : insns) {
    // Here we should reuse stack analysis to allow writes to known stack
    // location. But it is going to be a future optimization.
    if (i.writesMemory())
      return false;
  }

  eb.clear();
  cfg->getExitBasicBlock(eb);
  // The function entry block should have two edges,
  // one cond-taken, one cond-not-taken.
  //
  // One of the edge should point to an exit block
  // as the fast path exit block.
  std::vector<BPatch_edge*> edges;
  func_entry->getOutgoingEdges(edges);
  if (edges.size() != 2)
    return false;
  bool condTaken = false;
  bool condNotTaken = false;
  BPatch_basicBlock* fastExitBlock = NULL;
  for (auto e : edges) {
    if (e->getType() == CondJumpTaken)
      condTaken = true;
    if (e->getType() == CondJumpNottaken)
      condNotTaken = true;
    BPatch_basicBlock* b = e->getTarget();
    if (std::find(eb.begin(), eb.end(), b) != eb.end()) {
      fastExitBlock = b;
    } else {
      entry = b;
    }
  }
  if (!condTaken || !condNotTaken || fastExitBlock == NULL || entry == NULL)
    return false;

  // Function entry block cannot have intra-procedural incoming edges.
  edges.clear();
  func_entry->getIncomingEdges(edges);
  if (edges.size() > 0)
    return false;

  // The slow path entry should only have entry block as source.
  // Otherwise, the stack push instrumentation will be executed multiple times.
  edges.clear();
  entry->getIncomingEdges(edges);
  if (edges.size() != 1)
    return false;

  // The fast path exit block should contain one return instruction.
  // This condition makes sure that our shadow stack instrumentation can
  // find the correct location for return address.
  // TODO: relax this condition later.
  insns.clear();
  fastExitBlock->getInstructions(insns);
  if (insns.size() != 1)
    return false;
  if (insns[0].getCategory() != InstructionAPI::c_ReturnInsn)
    return false;

  // Excluding the function entry block,
  // each block that is a source block of the fast exit block
  // should be instrumented with shadow stack pop.
  edges.clear();
  fastExitBlock->getIncomingEdges(edges);
  for (auto e : edges) {
    if (e->getSource() != func_entry) {
      BPatch_basicBlock* slowPathExit = e->getSource();
      // If the slow path exit has more than one outgoing edges,
      // we cannot instrument at its exit, because stack pop operation
      // can potentially be performed mulitple times.
      std::vector<BPatch_edge*> out_edges;
      slowPathExit->getOutgoingEdges(out_edges);
      if (out_edges.size() != 1)
        return false;
      exits.push_back(e->getSource());
    }
  }

  // In addition, we need to instrument all non-fast-exit exit blocks.
  for (auto b : eb)
    if (b != fastExitBlock)
      exits.push_back(b);
  return true;
}
