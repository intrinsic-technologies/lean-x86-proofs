import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeComissXmmXmm (dst src : BitVec 4) : List UInt8 :=
  encodeSseRegReg 0x2F dst src

end X86Proofs
