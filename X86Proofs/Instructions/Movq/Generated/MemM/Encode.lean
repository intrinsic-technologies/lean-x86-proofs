import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovqM64Mm (src : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0x7F src am

end X86Proofs
