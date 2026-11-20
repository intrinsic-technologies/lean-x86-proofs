import X86Proofs.Step.SseEncode
import X86Proofs.Step.FetchImm

namespace X86Proofs

abbrev encodePinsrwMmR32Imm8 (dst : BitVec 3) (src : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  encodeMmxGpr 0xC4 dst src ++ immBytes 8 imm

end X86Proofs
