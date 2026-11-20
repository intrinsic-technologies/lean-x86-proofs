import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeTestM64R64 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  am.rexByte true src :: 0x85 :: am.modrm (regLow src) :: am.tail

def encodeTestM32R32 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  if am.NoRex src then 0x85 :: am.modrm (regLow src) :: am.tail
  else am.rexByte false src :: 0x85 :: am.modrm (regLow src) :: am.tail

def encodeTestM16R16 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  if am.NoRex src then 0x66 :: 0x85 :: am.modrm (regLow src) :: am.tail
  else 0x66 :: am.rexByte false src :: 0x85 :: am.modrm (regLow src) :: am.tail

end X86Proofs
