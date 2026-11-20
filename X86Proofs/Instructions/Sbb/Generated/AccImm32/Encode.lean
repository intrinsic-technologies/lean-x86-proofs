import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeSbbRaxImm32 (imm : BitVec 32) : List UInt8 :=
  0x48 :: 0x1D :: immBytes 32 imm

def encodeSbbEaxImm32 (imm : BitVec 32) : List UInt8 :=
  0x1D :: immBytes 32 imm

def encodeSbbAxImm16 (imm : BitVec 16) : List UInt8 :=
  0x66 :: 0x1D :: immBytes 16 imm

end X86Proofs
