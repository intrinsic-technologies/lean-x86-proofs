import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePmaddwdMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xF5 dst src

end X86Proofs
