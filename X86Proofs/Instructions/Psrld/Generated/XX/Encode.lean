import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsrldXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0x66 :: encodeSseRegReg 0xD2 dst src

end X86Proofs
