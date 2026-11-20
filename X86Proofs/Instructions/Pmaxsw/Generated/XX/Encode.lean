import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePmaxswXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0x66 :: encodeSseRegReg 0xEE dst src

end X86Proofs
