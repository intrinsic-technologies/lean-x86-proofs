import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePminubMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xDA dst src

end X86Proofs
