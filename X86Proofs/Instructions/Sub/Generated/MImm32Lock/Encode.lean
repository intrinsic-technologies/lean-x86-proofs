import X86Proofs.Instructions.Sub.Generated.MImm32.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeSubLockM64Imm32 (am : AddrMode) (imm : BitVec 32) : List UInt8 :=
  0xF0 :: encodeSubM64Imm32 am imm

def encodeSubLockM32Imm32 (am : AddrMode) (imm : BitVec 32) : List UInt8 :=
  0xF0 :: encodeSubM32Imm32 am imm

def encodeSubLockM16Imm16 (am : AddrMode) (imm : BitVec 16) : List UInt8 :=
  0xF0 :: encodeSubM16Imm16 am imm

end X86Proofs
