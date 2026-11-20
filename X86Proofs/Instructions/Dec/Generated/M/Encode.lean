import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeDecM64 (am : AddrMode) : List UInt8 :=
  am.rexByte true 0 :: 0xFF :: am.modrm 1 :: am.tail

def encodeDecM32 (am : AddrMode) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0xFF :: am.modrm 1 :: am.tail
  else am.rexByte false 0 :: 0xFF :: am.modrm 1 :: am.tail

def encodeDecM16 (am : AddrMode) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0x66 :: 0xFF :: am.modrm 1 :: am.tail
  else 0x66 :: am.rexByte false 0 :: 0xFF :: am.modrm 1 :: am.tail

end X86Proofs
