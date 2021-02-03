#include "gflags/gflags.h"
#include "glog/logging.h"
#include "parse.h"
#include "utils.h"
#include "PatchModifier.h"
#include "PatchCFG.h"
#include "BPatch_function.h"

#include <iostream>
#include <fstream>
#include <map>


using namespace Dyninst;
using namespace Dyninst::PatchAPI;

DECLARE_string(output);
DECLARE_string(inline_file);
DECLARE_bool(disable_inline);
extern CFGMaker* cfgMaker;
static std::map<std::pair<Address, Address>, bool> inlinePair;

void ReadFunctionInliningFile() {
  if (FLAGS_inline_file != "") {
    std::ifstream infile(FLAGS_inline_file, std::fstream::in);
    Address caller, callee;
    while (infile >> std::hex >> caller >> callee) {
      inlinePair[std::make_pair(caller, callee)] = true;
    }
  }
}

bool InlineFunctionCalls(BPatch_function* function, const litecfi::Parser& parser) {
  if (FLAGS_disable_inline) return false;
  PatchFunction* f = PatchAPI::convert(function);
  bool didInline = false;
  for (auto b : f->callBlocks()) {
    Address callee = 0;
    for (auto e : b->targets()) {
      if (e->type() == ParseAPI::CALL && !e->sinkEdge()) {
        callee = e->trg()->start();
      }
    } 
    if (callee == 0) continue;
    if (inlinePair.find(std::make_pair(f->addr(), callee)) == inlinePair.end()) continue;
    assert(PatchModifier::inlineFunction(cfgMaker, f, b));
    didInline = true;
  }
  return didInline;
}

