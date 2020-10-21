#ifndef SHADOWGUARD_SNIPPET_H
#define SHADOWGUARD_SNIPPET_H

#include "Snippet.h"
#include "jit.h"

#include "asmjit/asmjit.h"
#include "assembler.h"
#include "codegen.h"

namespace Dyninst {
  namespace PatchAPI {
    class Point;
    class PatchBlock;
  };
};

class StackOpSnippet : public Dyninst::PatchAPI::Snippet {
 public:
  explicit StackOpSnippet(FuncSummary* summary, bool u, int h, bool u2)
      : summary_(summary), useOriginalCode(u), height(h),
        useOriginalCodeFixed(u2) {}

  bool generate(Dyninst::PatchAPI::Point* pt, Dyninst::Buffer& buf) override;

 protected:
  std::string (*jit_fn_)(Dyninst::PatchAPI::Point* pt, FuncSummary* summary,
                         AssemblerHolder&, bool, int, bool);

 private:
  FuncSummary* summary_;
  bool useOriginalCode;
  int height;
  bool useOriginalCodeFixed;
};

class StackPushSnippet : public StackOpSnippet {
 public:
  explicit StackPushSnippet(FuncSummary* summary, bool u, int h = 0,
                            bool u2 = false)
      : StackOpSnippet(summary, u, h, u2) {
    jit_fn_ = JitStackPush;
  }
};

class StackPopSnippet : public StackOpSnippet {
 public:
  explicit StackPopSnippet(FuncSummary* summary, bool u)
      : StackOpSnippet(summary, u, 0, false) {
    jit_fn_ = JitStackPop;
  }
};

class RegisterPushSnippet : public StackOpSnippet {
 public:
  explicit RegisterPushSnippet(FuncSummary* summary, int height = 0)
      : StackOpSnippet(summary, false, height, false) {
    jit_fn_ = JitRegisterPush;
  }
};

class RegisterPopSnippet : public StackOpSnippet {
 public:
  explicit RegisterPopSnippet(FuncSummary* summary)
      : StackOpSnippet(summary, false, 0, false) {
    jit_fn_ = JitRegisterPop;
  }
};

class CallEmulatePushSnippet : public Dyninst::PatchAPI::Snippet {
 public:
  explicit CallEmulatePushSnippet(
    FuncSummary* summary, 
    int h, 
    bool u,
    Dyninst::PatchAPI::PatchBlock* block) : 
    summary_(summary), 
    height(h), 
    useOriginalCodeFixed(u),
    b(block) {
    jit_fn_ = JitCallEmulatePush;
  }
  bool generate(Dyninst::PatchAPI::Point* pt, Dyninst::Buffer& buf) override;

 protected:
  std::string (*jit_fn_)(Dyninst::PatchAPI::Point* pt, FuncSummary* summary,
                         AssemblerHolder&, int, bool);

 private:
  FuncSummary* summary_;    
  int height;  
  bool useOriginalCodeFixed;
  Dyninst::PatchAPI::PatchBlock* b;
};

#endif