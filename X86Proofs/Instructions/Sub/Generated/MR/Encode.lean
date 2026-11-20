import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeSubM64R64 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  am.rexByte true src :: 0x29 :: am.modrm (regLow src) :: am.tail

def encodeSubM32R32 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  if am.NoRex src then 0x29 :: am.modrm (regLow src) :: am.tail
  else am.rexByte false src :: 0x29 :: am.modrm (regLow src) :: am.tail

def encodeSubM16R16 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  if am.NoRex src then 0x66 :: 0x29 :: am.modrm (regLow src) :: am.tail
  else 0x66 :: am.rexByte false src :: 0x29 :: am.modrm (regLow src) :: am.tail

end X86Proofs
