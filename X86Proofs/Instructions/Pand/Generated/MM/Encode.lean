import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePandMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xDB dst src

end X86Proofs
