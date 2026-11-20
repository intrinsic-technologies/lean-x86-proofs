import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePmulhuwMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xE4 dst src

end X86Proofs
