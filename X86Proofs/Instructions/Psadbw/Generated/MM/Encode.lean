import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsadbwMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xF6 dst src

end X86Proofs
