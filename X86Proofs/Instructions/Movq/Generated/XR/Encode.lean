import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovqXmmR64 (dst src : BitVec 4) : List UInt8 :=
  0x66 :: encodeSseRegRegW 0x6E dst src

end X86Proofs
