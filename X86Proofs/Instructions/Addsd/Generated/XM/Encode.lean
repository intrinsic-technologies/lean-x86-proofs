import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeAddsdXmmM64 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF2 :: encodeSseMem 0x58 dst am

end X86Proofs
