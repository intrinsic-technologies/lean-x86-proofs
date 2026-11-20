import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeAndpsXmmXmm (dst src : BitVec 4) : List UInt8 :=
  encodeSseRegReg 0x54 dst src

end X86Proofs
