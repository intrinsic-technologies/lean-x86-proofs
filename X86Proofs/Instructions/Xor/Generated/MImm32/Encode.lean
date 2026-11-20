import X86Proofs.Step.Address
import X86Proofs.Step.FetchImm

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeXorM64Imm32 (am : AddrMode) (imm : BitVec 32) : List UInt8 :=
  am.rexByte true 0 :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 32 imm)

def encodeXorM32Imm32 (am : AddrMode) (imm : BitVec 32) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 32 imm)
  else am.rexByte false 0 :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 32 imm)

def encodeXorM16Imm16 (am : AddrMode) (imm : BitVec 16) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0x66 :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 16 imm)
  else 0x66 :: am.rexByte false 0 :: 0x81 :: am.modrm 6 :: (am.tail ++ immBytes 16 imm)

end X86Proofs
