import X86Proofs.Instructions.And.Generated.MImm32.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeAndLockM64Imm32 (am : AddrMode) (imm : BitVec 32) : List UInt8 :=
  0xF0 :: encodeAndM64Imm32 am imm

def encodeAndLockM32Imm32 (am : AddrMode) (imm : BitVec 32) : List UInt8 :=
  0xF0 :: encodeAndM32Imm32 am imm

def encodeAndLockM16Imm16 (am : AddrMode) (imm : BitVec 16) : List UInt8 :=
  0xF0 :: encodeAndM16Imm16 am imm

end X86Proofs
