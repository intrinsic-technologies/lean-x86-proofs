import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeCmpxchg8bM64 (am : AddrMode) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0x0F :: 0xC7 :: am.modrm 1 :: am.tail
  else am.rexByte false 0 :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail

end X86Proofs
