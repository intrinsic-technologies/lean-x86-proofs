import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMaskmovdquXmmXmm (src mask : BitVec 4) : List UInt8 :=
  0x66 :: encodeSseRegReg 0xF7 src mask

end X86Proofs
