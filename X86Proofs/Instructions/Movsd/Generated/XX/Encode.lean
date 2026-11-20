import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovsdXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0xF2 :: encodeSseRegReg 0x10 dst src

end X86Proofs
