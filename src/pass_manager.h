#ifndef LITECFI_PASS_MANAGER_H_
#define LITECFI_PASS_MANAGER_H_

#include <map>
#include <set>
#include <string>

#include "CodeObject.h"
#include "utils.h"

using namespace Dyninst;
using namespace Dyninst::ParseAPI;

struct FuncSummary {
  bool writesMemory;
  bool adjustSP;
  bool containsPLTCall;
  bool containsUnknownCF;
  std::set<Function*> callees;

  void Print() {
    printf("writesMemory=%d ", writesMemory);
    printf("adjustSP=%d ", adjustSP);
    printf("containsPLTCall=%d ", containsPLTCall);
    printf("containsUnknownCF=%d ", containsUnknownCF);
    printf("Callee=%lu\n", callees.size());
  }
};

class Pass {
 public:
  Pass(std::string name, std::string description)
      : pass_name_(name), description_(description) {}

  virtual void RunLocalAnalysis(CodeObject* co, Function* f, FuncSummary* s) {
    // NOOP
  }

  virtual void RunGlobalAnalysis(CodeObject* co,
                                 std::map<Function*, FuncSummary*>& summaries) {
    // NOOP
  }

  virtual bool IsSafeFunction(FuncSummary* s) {
    return !s->writesMemory && !s->adjustSP && !s->containsPLTCall &&
           !s->containsUnknownCF && s->callees.empty();
  }

  void RunPass(CodeObject* co, std::map<Function*, FuncSummary*>& summaries) {
    StdOut(Color::YELLOW) << "------------------------------------" << Endl;
    StdOut(Color::YELLOW) << "Running pass > " << pass_name_ << Endl;
    StdOut(Color::YELLOW) << "  Description : " << description_ << Endl;

    for (auto f : co->funcs()) {
      FuncSummary* s = summaries[f];
      if (s == nullptr) {
        s = new FuncSummary();
        summaries[f] = s;
      }
      RunLocalAnalysis(co, f, s);
    }

    RunGlobalAnalysis(co, summaries);

    long count = 0;
    for (auto f : co->funcs()) {
      FuncSummary* s = summaries[f];
      if (IsSafeFunction(s)) {
        ++count;
      }
    }

    StdOut(Color::YELLOW) << "  Safe Functions Found (cumulative) : " << count
                          << Endl;
  }

 protected:
  std::string pass_name_;
  std::string description_;
};

class PassManager {
 public:
  PassManager* AddPass(Pass* pass) {
    passes_.push_back(pass);
    return this;
  }

  std::set<Function*> Run(CodeObject* co) {
    for (Pass* p : passes_) {
      p->RunPass(co, summaries_);
    }

    std::set<Function*> safe;
    Pass* last = passes_.back();
    for (auto& it : summaries_) {
      if (last->IsSafeFunction(it.second)) {
        safe.insert(it.first);
      }
    }

    StdOut(Color::BLUE) << "\nSummary: " << Endl;
    StdOut(Color::BLUE) << "  Safe Functions Found : " << safe.size() << Endl;
    StdOut(Color::BLUE) << "  Non Safe Functions : "
                        << co->funcs().size() - safe.size() << Endl;

    return safe;
  }

 private:
  std::map<Function*, FuncSummary*> summaries_;
  std::vector<Pass*> passes_;
};

#endif  // LITECFI_PASS_MANAGER_H