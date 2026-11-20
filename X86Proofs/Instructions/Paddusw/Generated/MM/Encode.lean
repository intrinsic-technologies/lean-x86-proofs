import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePadduswMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xDD dst src

end X86Proofs
