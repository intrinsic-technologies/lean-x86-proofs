import X86Proofs.Instructions.Or.Generated.MImm32.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeOrLockM64Imm32 (am : AddrMode) (imm : BitVec 32) : List UInt8 :=
  0xF0 :: encodeOrM64Imm32 am imm

def encodeOrLockM32Imm32 (am : AddrMode) (imm : BitVec 32) : List UInt8 :=
  0xF0 :: encodeOrM32Imm32 am imm

def encodeOrLockM16Imm16 (am : AddrMode) (imm : BitVec 16) : List UInt8 :=
  0xF0 :: encodeOrM16Imm16 am imm

end X86Proofs
