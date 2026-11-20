import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePmulhuwXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0x66 :: encodeSseRegReg 0xE4 dst src

end X86Proofs
