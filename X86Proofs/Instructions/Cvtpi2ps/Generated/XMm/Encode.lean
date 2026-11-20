import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeCvtpi2psXmmMm (dst : BitVec 4) (src : BitVec 3) : List UInt8 :=
  encodeGprMmx 0x2A dst src

end X86Proofs
