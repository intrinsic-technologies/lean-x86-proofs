import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsubusbMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xD8 dst src

end X86Proofs
