import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeCvtsd2ssXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0xF2 :: encodeSseRegReg 0x5A dst src

end X86Proofs
