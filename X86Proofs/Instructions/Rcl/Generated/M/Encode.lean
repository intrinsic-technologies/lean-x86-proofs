import X86Proofs.Step.Address
import X86Proofs.Step.FetchImm

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeRclM64Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  am.rexByte true 0 :: 0xC1 :: am.modrm 2 :: (am.tail ++ immBytes 8 imm)

def encodeRclM32Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0xC1 :: am.modrm 2 :: (am.tail ++ immBytes 8 imm)
  else am.rexByte false 0 :: 0xC1 :: am.modrm 2 :: (am.tail ++ immBytes 8 imm)

def encodeRclM16Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0x66 :: 0xC1 :: am.modrm 2 :: (am.tail ++ immBytes 8 imm)
  else 0x66 :: am.rexByte false 0 :: 0xC1 :: am.modrm 2 :: (am.tail ++ immBytes 8 imm)

def encodeRclM64One (am : AddrMode) : List UInt8 :=
  am.rexByte true 0 :: 0xD1 :: am.modrm 2 :: am.tail

def encodeRclM32One (am : AddrMode) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0xD1 :: am.modrm 2 :: am.tail
  else am.rexByte false 0 :: 0xD1 :: am.modrm 2 :: am.tail

def encodeRclM16One (am : AddrMode) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0x66 :: 0xD1 :: am.modrm 2 :: am.tail
  else 0x66 :: am.rexByte false 0 :: 0xD1 :: am.modrm 2 :: am.tail

end X86Proofs
