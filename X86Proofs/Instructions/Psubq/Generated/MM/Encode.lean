import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsubqMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xFB dst src

end X86Proofs
