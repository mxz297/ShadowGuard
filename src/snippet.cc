#include "snippet.h"

//#include "PatchLabel.h"
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
/*	
    AssemblerHolder ah;
    jit_fn_(pt, summary_, ah, height, useOriginalCodeFixed);

    size_t size = ah.GetCode()->codeSize();
    char* temp_buf = (char*)malloc(size);

    ah.GetCode()->relocateToBase((uint64_t)temp_buf);

    size = ah.GetCode()->codeSize();
    ah.GetCode()->copyFlattenedData(temp_buf, size,
                                    asmjit::CodeHolder::kCopyWithPadding);

    Dyninst::InstructionAPI::InstructionDecoder decoder(temp_buf, size, Dyninst::Arch_x86_64);
    size_t offset = 0;
    while (offset < size) {
        Dyninst::InstructionAPI::Instruction i = decoder.decode();
        offset += i.size();
        if (i.getOperation().getID() == e_lea) break;        
    }    
    Dyninst::PatchAPI::PatchLabel::generateALabel(b, buf.curAddr() + offset - 4);                                    

    buf.copy(temp_buf, size);
*/
    return true;    
}
