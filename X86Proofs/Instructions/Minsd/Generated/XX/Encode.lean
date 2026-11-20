import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMinsdXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0xF2 :: encodeSseRegReg 0x5D dst src

end X86Proofs
