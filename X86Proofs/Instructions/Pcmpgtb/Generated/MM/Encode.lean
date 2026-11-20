import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePcmpgtbMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0x64 dst src

end X86Proofs
