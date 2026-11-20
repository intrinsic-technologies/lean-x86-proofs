import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeMovM32R32 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  if am.NoRex src then 0x89 :: am.modrm (regLow src) :: am.tail
  else am.rexByte false src :: 0x89 :: am.modrm (regLow src) :: am.tail

def encodeMovM16R16 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  if am.NoRex src then 0x66 :: 0x89 :: am.modrm (regLow src) :: am.tail
  else 0x66 :: am.rexByte false src :: 0x89 :: am.modrm (regLow src) :: am.tail

end X86Proofs
