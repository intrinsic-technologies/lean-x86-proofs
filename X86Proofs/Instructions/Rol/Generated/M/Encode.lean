import X86Proofs.Step.Address
import X86Proofs.Step.FetchImm

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeRolM64Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  am.rexByte true 0 :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)

def encodeRolM32Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)
  else am.rexByte false 0 :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)

def encodeRolM16Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0x66 :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)
  else 0x66 :: am.rexByte false 0 :: 0xC1 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)

def encodeRolM64One (am : AddrMode) : List UInt8 :=
  am.rexByte true 0 :: 0xD1 :: am.modrm 0 :: am.tail

def encodeRolM32One (am : AddrMode) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0xD1 :: am.modrm 0 :: am.tail
  else am.rexByte false 0 :: 0xD1 :: am.modrm 0 :: am.tail

def encodeRolM16One (am : AddrMode) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0x66 :: 0xD1 :: am.modrm 0 :: am.tail
  else 0x66 :: am.rexByte false 0 :: 0xD1 :: am.modrm 0 :: am.tail

end X86Proofs
