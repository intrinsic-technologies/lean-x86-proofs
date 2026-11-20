import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePmaddwdMmM64 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0xF5 dst am

end X86Proofs
