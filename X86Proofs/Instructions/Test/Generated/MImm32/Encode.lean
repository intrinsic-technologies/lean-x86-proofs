import X86Proofs.Step.Address
import X86Proofs.Step.FetchImm

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeTestM64Imm32 (am : AddrMode) (imm : BitVec 32) : List UInt8 :=
  am.rexByte true 0 :: 0xF7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)

def encodeTestM32Imm32 (am : AddrMode) (imm : BitVec 32) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0xF7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)
  else am.rexByte false 0 :: 0xF7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)

def encodeTestM16Imm16 (am : AddrMode) (imm : BitVec 16) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0x66 :: 0xF7 :: am.modrm 0 :: (am.tail ++ immBytes 16 imm)
  else 0x66 :: am.rexByte false 0 :: 0xF7 :: am.modrm 0 :: (am.tail ++ immBytes 16 imm)

end X86Proofs
