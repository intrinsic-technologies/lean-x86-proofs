import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePcmpgtdMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0x66 dst src

end X86Proofs
