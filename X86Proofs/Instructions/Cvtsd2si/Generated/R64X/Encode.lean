import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeCvtsd2siR64Xmm (dst src : BitVec 4) : List UInt8 :=
  0xF2 :: encodeSseRegRegW 0x2D dst src

end X86Proofs
