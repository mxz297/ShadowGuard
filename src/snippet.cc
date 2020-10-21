#include "snippet.h"

#include "PatchLabel.h"
#include "InstructionDecoder.h"
#include "Instruction.h"

bool StackOpSnippet::generate(Dyninst::PatchAPI::Point* pt, Dyninst::Buffer& buf) {
    AssemblerHolder ah;
    jit_fn_(pt, summary_, ah, useOriginalCode, height, useOriginalCodeFixed);

    size_t size = ah.GetCode()->codeSize();
    char* temp_buf = (char*)malloc(size);

    ah.GetCode()->relocateToBase((uint64_t)temp_buf);

    size = ah.GetCode()->codeSize();
    ah.GetCode()->copyFlattenedData(temp_buf, size,
                                    asmjit::CodeHolder::kCopyWithPadding);

    buf.copy(temp_buf, size);
    return true;    
}

bool CallEmulatePushSnippet::generate(Dyninst::PatchAPI::Point* pt, Dyninst::Buffer& buf) {
    AssemblerHolder ah;
    jit_fn_(pt, summary_, ah, height, useOriginalCodeFixed);

    size_t size = ah.GetCode()->codeSize();
    char* temp_buf = (char*)malloc(size);

    ah.GetCode()->relocateToBase((uint64_t)temp_buf);

    size = ah.GetCode()->codeSize();
    ah.GetCode()->copyFlattenedData(temp_buf, size,
                                    asmjit::CodeHolder::kCopyWithPadding);

    Dyninst::InstructionAPI::InstructionDecoder decoder(temp_buf, 15, Dyninst::Arch_x86_64);
    Dyninst::InstructionAPI::Instruction i = decoder.decode();
    Dyninst::PatchAPI::PatchLabel::generateALabel(b, buf.curAddr() + i.size() - 4);                                    

    buf.copy(temp_buf, size);
    return true;    
}