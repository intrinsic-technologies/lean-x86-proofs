import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovntqM64Mm (src : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0xE7 src am

end X86Proofs
