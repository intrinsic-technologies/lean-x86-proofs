import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsubwXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0x66 :: encodeSseRegReg 0xF9 dst src

end X86Proofs
