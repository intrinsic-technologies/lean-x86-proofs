import X86Proofs.Step.Address
import X86Proofs.Step.FetchImm

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeOrM64Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  am.rexByte true 0 :: 0x83 :: am.modrm 1 :: (am.tail ++ immBytes 8 imm)

def encodeOrM32Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0x83 :: am.modrm 1 :: (am.tail ++ immBytes 8 imm)
  else am.rexByte false 0 :: 0x83 :: am.modrm 1 :: (am.tail ++ immBytes 8 imm)

def encodeOrM16Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0x66 :: 0x83 :: am.modrm 1 :: (am.tail ++ immBytes 8 imm)
  else 0x66 :: am.rexByte false 0 :: 0x83 :: am.modrm 1 :: (am.tail ++ immBytes 8 imm)

end X86Proofs
