import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeCvtps2pdXmmXmm (dst src : BitVec 4) : List UInt8 :=
  encodeSseRegReg 0x5A dst src

end X86Proofs
