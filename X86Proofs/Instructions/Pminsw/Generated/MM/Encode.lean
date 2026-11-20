import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePminswMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xEA dst src

end X86Proofs
