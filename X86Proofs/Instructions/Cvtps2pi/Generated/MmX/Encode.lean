import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeCvtps2piMmXmm (dst : BitVec 3) (src : BitVec 4) : List UInt8 :=
  encodeMmxGpr 0x2D dst src

end X86Proofs
