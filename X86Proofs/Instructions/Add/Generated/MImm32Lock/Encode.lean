import X86Proofs.Instructions.Add.Generated.MImm32.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeAddLockM64Imm32 (am : AddrMode) (imm : BitVec 32) : List UInt8 :=
  0xF0 :: encodeAddM64Imm32 am imm

def encodeAddLockM32Imm32 (am : AddrMode) (imm : BitVec 32) : List UInt8 :=
  0xF0 :: encodeAddM32Imm32 am imm

def encodeAddLockM16Imm16 (am : AddrMode) (imm : BitVec 16) : List UInt8 :=
  0xF0 :: encodeAddM16Imm16 am imm

end X86Proofs
