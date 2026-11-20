import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePorMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xEB dst src

end X86Proofs
