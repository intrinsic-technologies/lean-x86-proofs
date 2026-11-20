import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeMovapdXmmM128 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  0x66 :: encodeSseMem 0x28 dst am

end X86Proofs
