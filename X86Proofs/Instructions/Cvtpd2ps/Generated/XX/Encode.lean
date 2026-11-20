import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeCvtpd2psXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0x66 :: encodeSseRegReg 0x5A dst src

end X86Proofs
