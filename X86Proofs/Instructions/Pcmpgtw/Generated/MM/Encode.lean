import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePcmpgtwMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0x65 dst src

end X86Proofs
