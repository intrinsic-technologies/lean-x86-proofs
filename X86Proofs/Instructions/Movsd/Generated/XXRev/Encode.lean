import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovsdXmmXmmRev (dst src : BitVec 4) : List UInt8 :=
  0xF2 :: encodeSseRegReg 0x11 src dst

end X86Proofs
