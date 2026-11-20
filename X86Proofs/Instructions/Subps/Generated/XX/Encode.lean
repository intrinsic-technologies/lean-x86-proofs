import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeSubpsXmmXmm (dst src : BitVec 4) : List UInt8 :=
  encodeSseRegReg 0x5C dst src

end X86Proofs
