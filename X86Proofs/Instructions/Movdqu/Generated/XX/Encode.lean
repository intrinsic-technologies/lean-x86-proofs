import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovdquXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0xF3 :: encodeSseRegReg 0x6F dst src

end X86Proofs
