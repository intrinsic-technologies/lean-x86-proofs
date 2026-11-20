import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeSqrtpsXmmXmm (dst src : BitVec 4) : List UInt8 :=
  encodeSseRegReg 0x51 dst src

end X86Proofs
