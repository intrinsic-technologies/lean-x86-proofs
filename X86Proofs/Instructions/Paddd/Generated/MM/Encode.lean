import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePadddMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xFE dst src

end X86Proofs
