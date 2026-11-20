import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeCvtdq2pdXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0xF3 :: encodeSseRegReg 0xE6 dst src

end X86Proofs
