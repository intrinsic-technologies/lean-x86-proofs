import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeCvtsi2sdXmmR32 (dst src : BitVec 4) : List UInt8 :=
  0xF2 :: encodeSseRegReg 0x2A dst src

end X86Proofs
