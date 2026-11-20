import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePaddusbXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0x66 :: encodeSseRegReg 0xDC dst src

end X86Proofs
