import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeMovqXmmM64 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF3 :: encodeSseMem 0x7E dst am

end X86Proofs
