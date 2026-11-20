import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeShlM64Cl (am : AddrMode) : List UInt8 :=
  am.rexByte true 0 :: 0xD3 :: am.modrm 4 :: am.tail

def encodeShlM32Cl (am : AddrMode) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0xD3 :: am.modrm 4 :: am.tail
  else am.rexByte false 0 :: 0xD3 :: am.modrm 4 :: am.tail

def encodeShlM16Cl (am : AddrMode) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0x66 :: 0xD3 :: am.modrm 4 :: am.tail
  else 0x66 :: am.rexByte false 0 :: 0xD3 :: am.modrm 4 :: am.tail

end X86Proofs
