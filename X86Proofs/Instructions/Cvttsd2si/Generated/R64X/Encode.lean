import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeCvttsd2siR64Xmm (dst src : BitVec 4) : List UInt8 :=
  0xF2 :: encodeSseRegRegW 0x2C dst src

end X86Proofs
