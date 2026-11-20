import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeMovR32M32 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  if am.NoRex dst then 0x8B :: am.modrm (regLow dst) :: am.tail
  else am.rexByte false dst :: 0x8B :: am.modrm (regLow dst) :: am.tail

def encodeMovR16M16 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  if am.NoRex dst then 0x66 :: 0x8B :: am.modrm (regLow dst) :: am.tail
  else 0x66 :: am.rexByte false dst :: 0x8B :: am.modrm (regLow dst) :: am.tail

end X86Proofs
