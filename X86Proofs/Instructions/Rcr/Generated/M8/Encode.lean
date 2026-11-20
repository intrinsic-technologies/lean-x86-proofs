import X86Proofs.Step.Address
import X86Proofs.Step.FetchImm

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeRcrM8Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0xC0 :: am.modrm 3 :: (am.tail ++ immBytes 8 imm)
  else am.rexByte false 0 :: 0xC0 :: am.modrm 3 :: (am.tail ++ immBytes 8 imm)

def encodeRcrM8One (am : AddrMode) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0xD0 :: am.modrm 3 :: am.tail
  else am.rexByte false 0 :: 0xD0 :: am.modrm 3 :: am.tail

end X86Proofs
