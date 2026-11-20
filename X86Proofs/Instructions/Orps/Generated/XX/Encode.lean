import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeOrpsXmmXmm (dst src : BitVec 4) : List UInt8 :=
  encodeSseRegReg 0x56 dst src

end X86Proofs
