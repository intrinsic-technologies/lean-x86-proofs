import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsrawMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xE1 dst src

end X86Proofs
