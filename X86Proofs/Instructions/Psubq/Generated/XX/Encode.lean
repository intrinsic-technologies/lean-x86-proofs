import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsubqXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0x66 :: encodeSseRegReg 0xFB dst src

end X86Proofs
