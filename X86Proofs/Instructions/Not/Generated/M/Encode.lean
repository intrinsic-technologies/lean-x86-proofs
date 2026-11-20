import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeNotM64 (am : AddrMode) : List UInt8 :=
  am.rexByte true 0 :: 0xF7 :: am.modrm 2 :: am.tail

def encodeNotM32 (am : AddrMode) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0xF7 :: am.modrm 2 :: am.tail
  else am.rexByte false 0 :: 0xF7 :: am.modrm 2 :: am.tail

def encodeNotM16 (am : AddrMode) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0x66 :: 0xF7 :: am.modrm 2 :: am.tail
  else 0x66 :: am.rexByte false 0 :: 0xF7 :: am.modrm 2 :: am.tail

end X86Proofs
