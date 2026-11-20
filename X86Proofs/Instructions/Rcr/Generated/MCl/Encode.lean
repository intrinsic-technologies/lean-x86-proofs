import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeRcrM64Cl (am : AddrMode) : List UInt8 :=
  am.rexByte true 0 :: 0xD3 :: am.modrm 3 :: am.tail

def encodeRcrM32Cl (am : AddrMode) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0xD3 :: am.modrm 3 :: am.tail
  else am.rexByte false 0 :: 0xD3 :: am.modrm 3 :: am.tail

def encodeRcrM16Cl (am : AddrMode) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0x66 :: 0xD3 :: am.modrm 3 :: am.tail
  else 0x66 :: am.rexByte false 0 :: 0xD3 :: am.modrm 3 :: am.tail

end X86Proofs
