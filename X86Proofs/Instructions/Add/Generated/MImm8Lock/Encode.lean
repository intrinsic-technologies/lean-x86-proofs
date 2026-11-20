import X86Proofs.Instructions.Add.Generated.MImm8.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeAddLockM64Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0xF0 :: encodeAddM64Imm8 am imm

def encodeAddLockM32Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0xF0 :: encodeAddM32Imm8 am imm

def encodeAddLockM16Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0xF0 :: encodeAddM16Imm8 am imm

end X86Proofs
