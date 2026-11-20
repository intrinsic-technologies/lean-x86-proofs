import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeMovdquXmmM128 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF3 :: encodeSseMem 0x6F dst am

end X86Proofs
