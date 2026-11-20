import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMulpsXmmXmm (dst src : BitVec 4) : List UInt8 :=
  encodeSseRegReg 0x59 dst src

end X86Proofs
