import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodePorXmmM128 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  0x66 :: encodeSseMem 0xEB dst am

end X86Proofs
