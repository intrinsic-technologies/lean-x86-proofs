import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovapsXmmXmm (dst src : BitVec 4) : List UInt8 :=
  encodeSseRegReg 0x28 dst src

end X86Proofs
