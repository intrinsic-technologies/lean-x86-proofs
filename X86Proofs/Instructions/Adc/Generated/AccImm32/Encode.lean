import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeAdcRaxImm32 (imm : BitVec 32) : List UInt8 :=
  0x48 :: 0x15 :: immBytes 32 imm

def encodeAdcEaxImm32 (imm : BitVec 32) : List UInt8 :=
  0x15 :: immBytes 32 imm

def encodeAdcAxImm16 (imm : BitVec 16) : List UInt8 :=
  0x66 :: 0x15 :: immBytes 16 imm

end X86Proofs
