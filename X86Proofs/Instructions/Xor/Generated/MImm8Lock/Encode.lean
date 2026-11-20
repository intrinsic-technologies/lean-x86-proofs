import X86Proofs.Instructions.Xor.Generated.MImm8.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeXorLockM64Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0xF0 :: encodeXorM64Imm8 am imm

def encodeXorLockM32Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0xF0 :: encodeXorM32Imm8 am imm

def encodeXorLockM16Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0xF0 :: encodeXorM16Imm8 am imm

end X86Proofs
