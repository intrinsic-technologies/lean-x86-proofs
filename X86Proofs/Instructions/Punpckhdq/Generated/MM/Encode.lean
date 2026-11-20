import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePunpckhdqMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0x6A dst src

end X86Proofs
