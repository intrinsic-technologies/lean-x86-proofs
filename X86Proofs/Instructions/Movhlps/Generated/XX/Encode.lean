import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovhlpsXmmXmm (dst src : BitVec 4) : List UInt8 :=
  encodeSseRegReg 0x12 dst src

end X86Proofs
