import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePmuludqMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xF4 dst src

end X86Proofs
