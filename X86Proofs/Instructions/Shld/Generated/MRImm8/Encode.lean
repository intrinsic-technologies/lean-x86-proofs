import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Step.Address
import X86Proofs.Core.Gpr

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeShldM64R64Imm8 (src : BitVec 4) (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  am.rexByte true src :: 0x0F :: 0xA4 :: am.modrm (regLow src) :: (am.tail ++ immBytes 8 imm)

def encodeShldM32R32Imm8 (src : BitVec 4) (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  if am.NoRex src then 0x0F :: 0xA4 :: am.modrm (regLow src) :: (am.tail ++ immBytes 8 imm)
  else am.rexByte false src :: 0x0F :: 0xA4 :: am.modrm (regLow src) :: (am.tail ++ immBytes 8 imm)

def encodeShldM16R16Imm8 (src : BitVec 4) (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  if am.NoRex src then 0x66 :: 0x0F :: 0xA4 :: am.modrm (regLow src) :: (am.tail ++ immBytes 8 imm)
  else 0x66 :: am.rexByte false src :: 0x0F :: 0xA4 :: am.modrm (regLow src) :: (am.tail ++ immBytes 8 imm)

end X86Proofs
