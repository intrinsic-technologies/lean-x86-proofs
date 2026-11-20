import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeFdivM64 (am : AddrMode) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0xDC :: am.modrm 6 :: am.tail
  else am.rexByte false 0 :: 0xDC :: am.modrm 6 :: am.tail

end X86Proofs
