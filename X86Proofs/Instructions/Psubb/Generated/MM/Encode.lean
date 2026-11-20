import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsubbMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xF8 dst src

end X86Proofs
