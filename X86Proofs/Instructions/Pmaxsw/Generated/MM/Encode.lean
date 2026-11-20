import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePmaxswMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xEE dst src

end X86Proofs
