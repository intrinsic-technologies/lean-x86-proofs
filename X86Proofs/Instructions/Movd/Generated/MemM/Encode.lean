import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovdM32Mm (src : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0x7E src am

end X86Proofs
