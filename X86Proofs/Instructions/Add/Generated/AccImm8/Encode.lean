import X86Proofs.Step.Prefix
import X86Proofs.Step.Decode
import X86Proofs.Step.FetchImm
import X86Proofs.Core.Gpr

namespace X86Proofs

def encodeAddAlImm8 (imm : BitVec 8) : List UInt8 :=
  0x04 :: immBytes 8 imm

end X86Proofs
