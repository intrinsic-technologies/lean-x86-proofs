import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePunpckhwdMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0x69 dst src

end X86Proofs
