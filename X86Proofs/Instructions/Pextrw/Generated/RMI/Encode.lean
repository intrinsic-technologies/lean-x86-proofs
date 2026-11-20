import X86Proofs.Step.SseEncode
import X86Proofs.Step.FetchImm

namespace X86Proofs

abbrev encodePextrwR32MmImm8 (dst : BitVec 4) (src : BitVec 3) (imm : BitVec 8) : List UInt8 :=
  encodeGprMmx 0xC5 dst src ++ immBytes 8 imm

end X86Proofs
