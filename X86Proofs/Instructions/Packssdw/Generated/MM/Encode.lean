import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePackssdwMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0x6B dst src

end X86Proofs
