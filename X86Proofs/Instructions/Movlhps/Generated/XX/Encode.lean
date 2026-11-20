import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovlhpsXmmXmm (dst src : BitVec 4) : List UInt8 :=
  encodeSseRegReg 0x16 dst src

end X86Proofs
