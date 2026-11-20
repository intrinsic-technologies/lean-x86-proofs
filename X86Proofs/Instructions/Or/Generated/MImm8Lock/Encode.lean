import X86Proofs.Instructions.Or.Generated.MImm8.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeOrLockM64Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0xF0 :: encodeOrM64Imm8 am imm

def encodeOrLockM32Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0xF0 :: encodeOrM32Imm8 am imm

def encodeOrLockM16Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0xF0 :: encodeOrM16Imm8 am imm

end X86Proofs
