import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePaddwMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xFD dst src

end X86Proofs
