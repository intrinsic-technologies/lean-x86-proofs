import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePxorXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0x66 :: encodeSseRegReg 0xEF dst src

end X86Proofs
