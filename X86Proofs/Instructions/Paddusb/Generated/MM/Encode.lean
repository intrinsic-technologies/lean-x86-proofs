import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePaddusbMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xDC dst src

end X86Proofs
