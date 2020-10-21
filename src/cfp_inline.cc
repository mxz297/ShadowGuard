#include "BPatch_function.h"

#include "PatchMgr.h"
#include "PatchModifier.h"
#include "Point.h"

#include "pass_manager.h"
#include "parse.h"
#include "utils.h"
#include "snippet.h"

#include <queue>
#include <vector>

using namespace Dyninst;
using namespace Dyninst::PatchAPI;

extern CFGMaker* cfgMaker;
extern int lowering_dead_reg_site;
extern int lowering_no_dead_reg_entry_site;
extern int lowering_no_dead_reg_exit_site;

DECLARE_bool(disable_reg_save_opt);

struct PriorityQueueItem {
  PatchBlock* b;
  int pathLen;
  bool operator< (const PriorityQueueItem & rhs) const {
    if (pathLen != rhs.pathLen) {
      return pathLen > rhs.pathLen;
    }
    return b->start() > rhs.b->start();
  }
  PriorityQueueItem(PatchBlock* bb, int len):
    b(bb), pathLen(len) {}
};

struct ShortestPathState {
  int curPathLen;
  PatchBlock* source;
};

static bool IdentifyInlinedPath(
  PatchFunction* f,
  vector<PatchBlock*> &inlinedBlocks
) {
  // The inlined path now is statically determined.
  // The chosen path should not contain any function call.
  // Right now, we choose a path that contains fewest bytes.
  // A PGO based strategy to combine path length with execution frequency
  // could be more effecitve.

  // Use dijkstra shortest path algorithm to find a path to inline
  std::unordered_map<PatchBlock*, ShortestPathState> s;
  for (auto b: f->blocks()) {
    s[b].curPathLen = std::numeric_limits<int>::max();
    s[b].source = nullptr;
  }
  s[f->entry()].curPathLen = 0;
  s[f->entry()].source = f->entry();

  std::priority_queue<PriorityQueueItem> q;
  q.push(PriorityQueueItem(f->entry(), 0));

  std::set<PatchBlock*> reachedRetBlocks;
  while (!q.empty()) {
    PriorityQueueItem item = q.top();
    q.pop();
    if (item.pathLen != s[item.b].curPathLen) continue;
    bool isRetBlock = false;
    bool isCallBlock = false;
    bool hasIndirectJump = false;
    for (auto e: item.b->targets()) {
      if (e->type() == ParseAPI::INDIRECT) hasIndirectJump = true;
      if (e->type() == ParseAPI::CALL) isCallBlock = true;
      // It is possible that a return does not have any return edge
      // if the function is called indirectly.
      // In this case, we cannot inline such function any way;
      // so we ignore such return block
      if (e->type() == ParseAPI::RET) isRetBlock = true;
    }
    if (isRetBlock) {
      reachedRetBlocks.insert(item.b);
      continue;
    }
    // Do not inline path that contains a call or indirect jump.
    // So, just treat the block as if there is no outgoing edge
    if (isCallBlock || hasIndirectJump) continue;

    // Update shortest path states for target blocks
    int blockLen = item.b->end() - item.b->start();
    for (auto e: item.b->targets()) {
      if (e->interproc() || e->sinkEdge()) continue;
      PatchBlock* target = e->trg();
      if (item.pathLen + blockLen < s[target].curPathLen) {
        s[target].curPathLen = item.pathLen + blockLen;
        s[target].source = item.b;
        q.push(PriorityQueueItem(target, s[target].curPathLen));
      }
    }
  }

  int shortestPath = std::numeric_limits<int>::max();
  PatchBlock* chosenRetBlock = nullptr;
  for (auto b : reachedRetBlocks) {
    if (s[b].curPathLen < shortestPath) {
      shortestPath = s[b].curPathLen;
      chosenRetBlock = b;
    }
  }

  if (chosenRetBlock == nullptr) return false;
  while (chosenRetBlock != f->entry()) {
    inlinedBlocks.emplace_back(chosenRetBlock);
    chosenRetBlock = s[chosenRetBlock].source;
  }
  inlinedBlocks.emplace_back(f->entry());
  std::reverse(std::begin(inlinedBlocks), std::end(inlinedBlocks));
  return true;
}

static PatchFunction* GetFuncContainingBlock(
  PatchBlock* b
) {
  std::vector<PatchFunction*> funcs;
  b->getFuncs(back_inserter(funcs));
  if (funcs.empty() || funcs.size() > 1) return nullptr;
  return funcs[0];
}

static void InlineBlocks(
  PatchBlock* callsite,
  PatchBlock* callft_block,
  std::vector<PatchBlock*> &inlinedBlocks,
  std::map<PatchBlock*, PatchBlock*> &cloneBlockMap
) {
  assert(callft_block != nullptr);

  // Split the call site to get rid of the call instruction
  assert(PatchModifier::split(callsite, callsite->last(), true, callsite->last()));

  // Redirect the callsite edge to the inlined entry  
  PatchEdge * start_inline_edge = nullptr;
  for (auto e : callsite->targets()) {
    if (e->type() == ParseAPI::FALLTHROUGH) start_inline_edge = e;
  }
  assert(start_inline_edge != nullptr);
  assert(PatchModifier::redirect(start_inline_edge, cloneBlockMap[inlinedBlocks[0]]));

  // Chain the inlined function blocks
  for (size_t i = 0; i < inlinedBlocks.size() - 1; ++i) {    
    PatchEdge* edge_to_redirect = nullptr;
    for (auto e : cloneBlockMap[inlinedBlocks[i]]->targets()) {
      if (e->trg() == inlinedBlocks[i+1]) {
        edge_to_redirect = e;
        break;
      }
    }
    assert(edge_to_redirect != nullptr);
    if (i == inlinedBlocks.size() - 2) {
      // The original source block goes to a return block.
      // After inlining, this block goes to the call fall-through block
      assert(PatchModifier::redirect(edge_to_redirect, callft_block));
    } else {
      assert(PatchModifier::redirect(edge_to_redirect, cloneBlockMap[inlinedBlocks[i+1]]));
    }    
  }
}

static void InstrumentNonInlinedEdges(  
  std::vector<PatchBlock*> &inlinedBlocks,
  std::map<PatchBlock*, PatchBlock*> &cloneBlockMap,
  FuncSummary* summary,
  PatchMgr::Ptr patcher,
  PatchBlock* callft_block,
  PatchFunction* f
) {
  for (auto b : inlinedBlocks) {
    for (auto e: b->targets()) {      
      if (cloneBlockMap.find(e->trg()) != cloneBlockMap.end()) continue;
      assert(summary->blockEndSPHeight.find(e->src()->start()) !=
            summary->blockEndSPHeight.end());
      int height = summary->blockEndSPHeight[e->src()->start()];
      MoveInstData* mid = summary->getMoveInstDataFixedAtEntry(e->trg()->start());
      if (FLAGS_disable_reg_save_opt) mid = nullptr;
      Snippet::Ptr stack_push;
      if (mid == nullptr) {
        lowering_dead_reg_site += 1;
        lowering_no_dead_reg_entry_site += 1;
        stack_push = CallEmulatePushSnippet::create(
            new CallEmulatePushSnippet(summary, height, false, callft_block));
      } else {
        lowering_dead_reg_site += 1;
        stack_push = CallEmulatePushSnippet::create(
            new CallEmulatePushSnippet(summary, height, true, callft_block));
      }

      Point* p = patcher->findPoint(PatchAPI::Location::EdgeInstance(f, e),
                                    Point::EdgeDuring);
      assert(p);
      p->pushBack(stack_push);
    }
  }
}

bool ControlFlowPathInlining(BPatch_function* function, FuncSummary* summary,
                             const litecfi::Parser& parser,
                             PatchMgr::Ptr patcher) {
  PatchFunction* f = PatchAPI::convert(function);

  // 1. Identify a path to inline.
  vector<PatchBlock*> inlinedBlocks;
  if (!IdentifyInlinedPath(f, inlinedBlocks)) {
    return false;
  }

  // 2. Iterate every callsite of this function
  for (auto e: f->entry()->sources()) {
    if (e->type() != ParseAPI::CALL) continue;
    PatchFunction * caller = GetFuncContainingBlock(e->src());
    if (caller == nullptr) continue;

    PatchBlock* call_ft_block = nullptr;
    for (auto te : e->src()->targets()) {
      if (te->type() == ParseAPI::CALL_FT) {
        call_ft_block = te->trg();
        break;
      }
    }

    // 2.1 Clone the blocks on the path.
    std::map<PatchBlock*, PatchBlock*> cloneBlockMap;
    for (auto b : inlinedBlocks) {
      PatchBlock* cloneB = cfgMaker->cloneBlock(b, b->object());
      cloneBlockMap[b] = cloneB;
      PatchModifier::addBlockToFunction(caller, cloneB);
    }

    // 2.2 Inline the cloned blocks
    InlineBlocks(e->src(), call_ft_block, inlinedBlocks, cloneBlockMap);

    // 2.3. Insert shadow stack push to edges
    InstrumentNonInlinedEdges(inlinedBlocks, cloneBlockMap, summary, patcher, call_ft_block, caller);
  }
}

