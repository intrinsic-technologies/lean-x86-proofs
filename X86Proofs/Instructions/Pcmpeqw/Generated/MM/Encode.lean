import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePcmpeqwMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0x75 dst src

end X86Proofs
