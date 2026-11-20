import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsubwMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xF9 dst src

end X86Proofs
