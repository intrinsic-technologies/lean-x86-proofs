import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodePushM64 (am : AddrMode) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0xFF :: am.modrm 6 :: am.tail
  else am.rexByte false 0 :: 0xFF :: am.modrm 6 :: am.tail

def encodePushM16 (am : AddrMode) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0x66 :: 0xFF :: am.modrm 6 :: am.tail
  else 0x66 :: am.rexByte false 0 :: 0xFF :: am.modrm 6 :: am.tail

end X86Proofs
