import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsllwMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xF1 dst src

end X86Proofs
