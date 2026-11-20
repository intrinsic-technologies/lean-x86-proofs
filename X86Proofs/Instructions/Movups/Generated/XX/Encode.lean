import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovupsXmmXmm (dst src : BitVec 4) : List UInt8 :=
  encodeSseRegReg 0x10 dst src

end X86Proofs
