import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Step.Address
import X86Proofs.Core.Gpr

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeShldM64R64Cl (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  am.rexByte true src :: 0x0F :: 0xA5 :: am.modrm (regLow src) :: am.tail

def encodeShldM32R32Cl (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  if am.NoRex src then 0x0F :: 0xA5 :: am.modrm (regLow src) :: am.tail
  else am.rexByte false src :: 0x0F :: 0xA5 :: am.modrm (regLow src) :: am.tail

def encodeShldM16R16Cl (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  if am.NoRex src then 0x66 :: 0x0F :: 0xA5 :: am.modrm (regLow src) :: am.tail
  else 0x66 :: am.rexByte false src :: 0x0F :: 0xA5 :: am.modrm (regLow src) :: am.tail

end X86Proofs
