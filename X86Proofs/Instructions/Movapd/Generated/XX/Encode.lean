import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovapdXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0x66 :: encodeSseRegReg 0x28 dst src

end X86Proofs
