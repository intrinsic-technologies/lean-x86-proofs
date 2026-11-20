import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovq2dqXmmMm (dst : BitVec 4) (src : BitVec 3) : List UInt8 :=
  0xF3 :: encodeGprMmx 0xD6 dst src

end X86Proofs
