import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeAddpsXmmXmm (dst src : BitVec 4) : List UInt8 :=
  encodeSseRegReg 0x58 dst src

end X86Proofs
