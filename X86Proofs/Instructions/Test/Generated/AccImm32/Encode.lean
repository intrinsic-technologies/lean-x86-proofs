import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeTestRaxImm32 (imm : BitVec 32) : List UInt8 :=
  0x48 :: 0xA9 :: immBytes 32 imm

def encodeTestEaxImm32 (imm : BitVec 32) : List UInt8 :=
  0xA9 :: immBytes 32 imm

def encodeTestAxImm16 (imm : BitVec 16) : List UInt8 :=
  0x66 :: 0xA9 :: immBytes 16 imm

end X86Proofs
