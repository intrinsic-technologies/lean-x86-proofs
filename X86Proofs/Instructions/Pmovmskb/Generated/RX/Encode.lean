import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePmovmskbR32Xmm (dst src : BitVec 4) : List UInt8 :=
  0x66 :: encodeSseRegReg 0xD7 dst src

end X86Proofs
