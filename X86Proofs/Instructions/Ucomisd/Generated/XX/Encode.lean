import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeUcomisdXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0x66 :: encodeSseRegReg 0x2E dst src

end X86Proofs
