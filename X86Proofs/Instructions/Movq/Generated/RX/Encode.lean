import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovqR64Xmm (dst src : BitVec 4) : List UInt8 :=
  0x66 :: encodeSseRegRegW 0x7E src dst

end X86Proofs
