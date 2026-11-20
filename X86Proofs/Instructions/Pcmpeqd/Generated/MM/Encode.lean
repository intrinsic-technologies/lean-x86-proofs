import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePcmpeqdMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0x76 dst src

end X86Proofs
