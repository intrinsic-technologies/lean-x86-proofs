import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePaddqMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xD4 dst src

end X86Proofs
