import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.Address
import X86Proofs.Core.Gpr

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeMovsxR64M8 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  am.rexByte true dst :: 0x0F :: 0xBE :: am.modrm (regLow dst) :: am.tail

def encodeMovsxR32M8 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  if am.NoRex dst then 0x0F :: 0xBE :: am.modrm (regLow dst) :: am.tail
  else am.rexByte false dst :: 0x0F :: 0xBE :: am.modrm (regLow dst) :: am.tail

def encodeMovsxR16M8 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  if am.NoRex dst then 0x66 :: 0x0F :: 0xBE :: am.modrm (regLow dst) :: am.tail
  else 0x66 :: am.rexByte false dst :: 0x0F :: 0xBE :: am.modrm (regLow dst) :: am.tail

end X86Proofs
