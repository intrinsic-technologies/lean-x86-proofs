import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovdquXmmXmmRev (dst src : BitVec 4) : List UInt8 :=
  0xF3 :: encodeSseRegReg 0x7F src dst

end X86Proofs
