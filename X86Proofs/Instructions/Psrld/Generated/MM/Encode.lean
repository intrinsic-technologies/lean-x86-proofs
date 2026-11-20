import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsrldMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xD2 dst src

end X86Proofs
