import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodePopM64 (am : AddrMode) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0x8F :: am.modrm 0 :: am.tail
  else am.rexByte false 0 :: 0x8F :: am.modrm 0 :: am.tail

def encodePopM16 (am : AddrMode) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0x66 :: 0x8F :: am.modrm 0 :: am.tail
  else 0x66 :: am.rexByte false 0 :: 0x8F :: am.modrm 0 :: am.tail

end X86Proofs
