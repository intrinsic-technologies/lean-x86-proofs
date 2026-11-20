import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePmovmskbR32Mm (dst : BitVec 4) (src : BitVec 3) : List UInt8 :=
  encodeGprMmx 0xD7 dst src

end X86Proofs
