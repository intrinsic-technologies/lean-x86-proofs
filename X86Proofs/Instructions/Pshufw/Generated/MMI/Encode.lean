import X86Proofs.Step.SseEncode
import X86Proofs.Step.FetchImm

namespace X86Proofs

abbrev encodePshufwMmMmImm8 (dst src : BitVec 3) (imm : BitVec 8) : List UInt8 :=
  encodeMmxRegReg 0x70 dst src ++ immBytes 8 imm

end X86Proofs
