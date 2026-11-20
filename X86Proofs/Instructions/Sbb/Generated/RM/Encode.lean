import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeSbbR64M64 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  am.rexByte true dst :: 0x1B :: am.modrm (regLow dst) :: am.tail

def encodeSbbR32M32 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  if am.NoRex dst then 0x1B :: am.modrm (regLow dst) :: am.tail
  else am.rexByte false dst :: 0x1B :: am.modrm (regLow dst) :: am.tail

def encodeSbbR16M16 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  if am.NoRex dst then 0x66 :: 0x1B :: am.modrm (regLow dst) :: am.tail
  else 0x66 :: am.rexByte false dst :: 0x1B :: am.modrm (regLow dst) :: am.tail

end X86Proofs
