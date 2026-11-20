import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePavgbMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xE0 dst src

end X86Proofs
