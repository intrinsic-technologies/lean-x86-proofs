import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePaddswMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xED dst src

end X86Proofs
