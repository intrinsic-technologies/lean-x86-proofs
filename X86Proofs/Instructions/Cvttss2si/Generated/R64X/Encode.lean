import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeCvttss2siR64Xmm (dst src : BitVec 4) : List UInt8 :=
  0xF3 :: encodeSseRegRegW 0x2C dst src

end X86Proofs
