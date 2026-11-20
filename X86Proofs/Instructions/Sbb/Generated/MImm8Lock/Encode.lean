import X86Proofs.Instructions.Sbb.Generated.MImm8.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeSbbLockM64Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0xF0 :: encodeSbbM64Imm8 am imm

def encodeSbbLockM32Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0xF0 :: encodeSbbM32Imm8 am imm

def encodeSbbLockM16Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0xF0 :: encodeSbbM16Imm8 am imm

end X86Proofs
