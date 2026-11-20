import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeImulM8 (am : AddrMode) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0xF6 :: am.modrm 5 :: am.tail
  else am.rexByte false 0 :: 0xF6 :: am.modrm 5 :: am.tail

end X86Proofs
