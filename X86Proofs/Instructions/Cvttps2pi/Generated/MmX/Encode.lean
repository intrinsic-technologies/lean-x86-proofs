import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeCvttps2piMmXmm (dst : BitVec 3) (src : BitVec 4) : List UInt8 :=
  encodeMmxGpr 0x2C dst src

end X86Proofs
