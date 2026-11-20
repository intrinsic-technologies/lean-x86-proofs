import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeRsqrtssXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0xF3 :: encodeSseRegReg 0x52 dst src

end X86Proofs
