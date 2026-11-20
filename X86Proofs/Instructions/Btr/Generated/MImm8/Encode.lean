import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Step.Address
import X86Proofs.Core.Gpr

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeBtrM64Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  am.rexByte true 0 :: 0x0F :: 0xBA :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)

def encodeBtrM32Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0x0F :: 0xBA :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)
  else am.rexByte false 0 :: 0x0F :: 0xBA :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)

def encodeBtrM16Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0x66 :: 0x0F :: 0xBA :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)
  else 0x66 :: am.rexByte false 0 :: 0x0F :: 0xBA :: am.modrm 6 :: (am.tail ++ immBytes 8 imm)

end X86Proofs
