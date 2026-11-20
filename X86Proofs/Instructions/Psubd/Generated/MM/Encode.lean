import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsubdMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xFA dst src

end X86Proofs
