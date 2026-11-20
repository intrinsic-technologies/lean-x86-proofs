import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovssXmmXmmRev (dst src : BitVec 4) : List UInt8 :=
  0xF3 :: encodeSseRegReg 0x11 src dst

end X86Proofs
