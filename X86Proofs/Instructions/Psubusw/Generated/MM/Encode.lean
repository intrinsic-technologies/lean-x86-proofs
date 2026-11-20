import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsubuswMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xD9 dst src

end X86Proofs
