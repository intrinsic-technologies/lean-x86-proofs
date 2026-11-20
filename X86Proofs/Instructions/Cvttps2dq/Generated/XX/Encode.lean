import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeCvttps2dqXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0xF3 :: encodeSseRegReg 0x5B dst src

end X86Proofs
