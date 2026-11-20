import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePmullwMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xD5 dst src

end X86Proofs
