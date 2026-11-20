import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePcmpeqbMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0x74 dst src

end X86Proofs
