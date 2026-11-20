import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeTestM8R8 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  if src.toNat < 4 ∧ am.rexX = 0 ∧ am.rexB = 0 then 0x84 :: am.modrm (regLow src) :: am.tail
  else am.rexByte false src :: 0x84 :: am.modrm (regLow src) :: am.tail

def encodeTestM8R8NoRex (src : BitVec 3) (am : AddrMode) : List UInt8 :=
  0x84 :: am.modrm src :: am.tail

end X86Proofs
