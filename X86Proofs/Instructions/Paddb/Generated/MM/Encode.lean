import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePaddbMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xFC dst src

end X86Proofs
