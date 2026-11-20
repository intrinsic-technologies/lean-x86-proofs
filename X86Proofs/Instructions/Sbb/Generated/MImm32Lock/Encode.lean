import X86Proofs.Instructions.Sbb.Generated.MImm32.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeSbbLockM64Imm32 (am : AddrMode) (imm : BitVec 32) : List UInt8 :=
  0xF0 :: encodeSbbM64Imm32 am imm

def encodeSbbLockM32Imm32 (am : AddrMode) (imm : BitVec 32) : List UInt8 :=
  0xF0 :: encodeSbbM32Imm32 am imm

def encodeSbbLockM16Imm16 (am : AddrMode) (imm : BitVec 16) : List UInt8 :=
  0xF0 :: encodeSbbM16Imm16 am imm

end X86Proofs
