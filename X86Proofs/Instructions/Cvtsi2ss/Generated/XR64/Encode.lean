import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeCvtsi2ssXmmR64 (dst src : BitVec 4) : List UInt8 :=
  0xF3 :: encodeSseRegRegW 0x2A dst src

end X86Proofs
