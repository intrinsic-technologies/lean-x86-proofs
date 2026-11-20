import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsllqMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xF3 dst src

end X86Proofs
