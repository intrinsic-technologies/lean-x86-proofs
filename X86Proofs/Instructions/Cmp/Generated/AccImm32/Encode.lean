import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeCmpRaxImm32 (imm : BitVec 32) : List UInt8 :=
  0x48 :: 0x3D :: immBytes 32 imm

def encodeCmpEaxImm32 (imm : BitVec 32) : List UInt8 :=
  0x3D :: immBytes 32 imm

def encodeCmpAxImm16 (imm : BitVec 16) : List UInt8 :=
  0x66 :: 0x3D :: immBytes 16 imm

end X86Proofs
