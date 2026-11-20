import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePandnMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xDF dst src

end X86Proofs
