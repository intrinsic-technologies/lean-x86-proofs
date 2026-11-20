import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Step.Address
import X86Proofs.Core.Gpr

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeImulR64M64Imm32 (dst : BitVec 4) (am : AddrMode) (imm : BitVec 32) : List UInt8 :=
  am.rexByte true dst :: 0x69 :: am.modrm (regLow dst) :: (am.tail ++ immBytes 32 imm)

def encodeImulR32M32Imm32 (dst : BitVec 4) (am : AddrMode) (imm : BitVec 32) : List UInt8 :=
  if am.NoRex dst then 0x69 :: am.modrm (regLow dst) :: (am.tail ++ immBytes 32 imm)
  else am.rexByte false dst :: 0x69 :: am.modrm (regLow dst) :: (am.tail ++ immBytes 32 imm)

def encodeImulR16M16Imm16 (dst : BitVec 4) (am : AddrMode) (imm : BitVec 16) : List UInt8 :=
  if am.NoRex dst then 0x66 :: 0x69 :: am.modrm (regLow dst) :: (am.tail ++ immBytes 16 imm)
  else 0x66 :: am.rexByte false dst :: 0x69 :: am.modrm (regLow dst) :: (am.tail ++ immBytes 16 imm)

end X86Proofs
