import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePackuswbMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0x67 dst src

end X86Proofs
