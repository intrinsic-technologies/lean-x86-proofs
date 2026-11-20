import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeSubpdXmmM128 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  0x66 :: encodeSseMem 0x5C dst am

end X86Proofs
