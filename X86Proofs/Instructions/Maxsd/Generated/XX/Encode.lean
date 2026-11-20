import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMaxsdXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0xF2 :: encodeSseRegReg 0x5F dst src

end X86Proofs
