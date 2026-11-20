import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePunpckhdqXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0x66 :: encodeSseRegReg 0x6A dst src

end X86Proofs
