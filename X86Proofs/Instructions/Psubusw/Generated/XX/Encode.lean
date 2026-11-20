import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsubuswXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0x66 :: encodeSseRegReg 0xD9 dst src

end X86Proofs
