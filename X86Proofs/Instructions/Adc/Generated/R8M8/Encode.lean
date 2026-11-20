import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeAdcR8M8 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  if dst.toNat < 4 ∧ am.rexX = 0 ∧ am.rexB = 0 then 0x12 :: am.modrm (regLow dst) :: am.tail
  else am.rexByte false dst :: 0x12 :: am.modrm (regLow dst) :: am.tail

def encodeAdcR8M8NoRex (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  0x12 :: am.modrm dst :: am.tail

end X86Proofs
