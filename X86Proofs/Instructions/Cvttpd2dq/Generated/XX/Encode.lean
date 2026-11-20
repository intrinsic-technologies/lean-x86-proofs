import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeCvttpd2dqXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0x66 :: encodeSseRegReg 0xE6 dst src

end X86Proofs
