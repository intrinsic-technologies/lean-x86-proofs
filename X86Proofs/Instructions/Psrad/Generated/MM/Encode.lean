import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsradMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xE2 dst src

end X86Proofs
