import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeAndpdXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0x66 :: encodeSseRegReg 0x54 dst src

end X86Proofs
