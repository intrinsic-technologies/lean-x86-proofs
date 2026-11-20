import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsubswMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xE9 dst src

end X86Proofs
