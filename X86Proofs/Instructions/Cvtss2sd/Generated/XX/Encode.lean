import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeCvtss2sdXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0xF3 :: encodeSseRegReg 0x5A dst src

end X86Proofs
