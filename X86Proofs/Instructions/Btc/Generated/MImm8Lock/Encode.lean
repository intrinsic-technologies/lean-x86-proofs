import X86Proofs.Instructions.Btc.Generated.MImm8.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeBtcLockM64Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0xF0 :: encodeBtcM64Imm8 am imm

def encodeBtcLockM32Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0xF0 :: encodeBtcM32Imm8 am imm

def encodeBtcLockM16Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0xF0 :: encodeBtcM16Imm8 am imm

end X86Proofs
