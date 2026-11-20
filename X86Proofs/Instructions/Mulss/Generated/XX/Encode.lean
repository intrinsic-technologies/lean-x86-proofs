import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMulssXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0xF3 :: encodeSseRegReg 0x59 dst src

end X86Proofs
