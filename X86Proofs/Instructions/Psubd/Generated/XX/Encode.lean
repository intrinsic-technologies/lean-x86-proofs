import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsubdXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0x66 :: encodeSseRegReg 0xFA dst src

end X86Proofs
