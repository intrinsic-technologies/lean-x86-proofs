import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsubsbMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xE8 dst src

end X86Proofs
