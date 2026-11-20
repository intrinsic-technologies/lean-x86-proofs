import X86Proofs.Instructions.Btr.Generated.MImm8.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeBtrLockM64Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0xF0 :: encodeBtrM64Imm8 am imm

def encodeBtrLockM32Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0xF0 :: encodeBtrM32Imm8 am imm

def encodeBtrLockM16Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0xF0 :: encodeBtrM16Imm8 am imm

end X86Proofs
