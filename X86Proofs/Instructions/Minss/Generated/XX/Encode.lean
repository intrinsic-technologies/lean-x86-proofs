import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMinssXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0xF3 :: encodeSseRegReg 0x5D dst src

end X86Proofs
