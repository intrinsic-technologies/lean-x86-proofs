import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.Address
import X86Proofs.Core.Gpr

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeLzcntR64M64 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF3 :: am.rexByte true dst :: 0x0F :: 0xBD :: am.modrm (regLow dst) :: am.tail

def encodeLzcntR32M32 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  if am.NoRex dst then 0xF3 :: 0x0F :: 0xBD :: am.modrm (regLow dst) :: am.tail
  else 0xF3 :: am.rexByte false dst :: 0x0F :: 0xBD :: am.modrm (regLow dst) :: am.tail

def encodeLzcntR16M16 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  0x66 :: 0xF3 :: 0x0F :: 0xBD :: am.modrm dst :: am.tail

end X86Proofs
