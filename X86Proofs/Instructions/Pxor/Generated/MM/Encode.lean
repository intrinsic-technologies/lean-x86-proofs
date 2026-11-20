import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePxorMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xEF dst src

end X86Proofs
