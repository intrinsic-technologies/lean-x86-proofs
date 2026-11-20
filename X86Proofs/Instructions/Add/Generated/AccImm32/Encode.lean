import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeAddRaxImm32 (imm : BitVec 32) : List UInt8 :=
  0x48 :: 0x05 :: immBytes 32 imm

def encodeAddEaxImm32 (imm : BitVec 32) : List UInt8 :=
  0x05 :: immBytes 32 imm

def encodeAddAxImm16 (imm : BitVec 16) : List UInt8 :=
  0x66 :: 0x05 :: immBytes 16 imm

end X86Proofs
