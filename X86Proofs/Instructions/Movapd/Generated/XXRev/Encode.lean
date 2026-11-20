import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovapdXmmXmmRev (dst src : BitVec 4) : List UInt8 :=
  0x66 :: encodeSseRegReg 0x29 src dst

end X86Proofs
