import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePunpckhbwMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0x68 dst src

end X86Proofs
