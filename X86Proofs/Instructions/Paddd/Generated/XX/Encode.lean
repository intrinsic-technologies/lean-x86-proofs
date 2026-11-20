import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePadddXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0x66 :: encodeSseRegReg 0xFE dst src

end X86Proofs
