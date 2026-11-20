import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeRolM8Cl (am : AddrMode) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0xD2 :: am.modrm 0 :: am.tail
  else am.rexByte false 0 :: 0xD2 :: am.modrm 0 :: am.tail

end X86Proofs
