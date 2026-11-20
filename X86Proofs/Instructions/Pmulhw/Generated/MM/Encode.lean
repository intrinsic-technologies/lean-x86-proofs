import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePmulhwMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xE5 dst src

end X86Proofs
