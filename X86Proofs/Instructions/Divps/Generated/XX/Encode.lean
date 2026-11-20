import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeDivpsXmmXmm (dst src : BitVec 4) : List UInt8 :=
  encodeSseRegReg 0x5E dst src

end X86Proofs
