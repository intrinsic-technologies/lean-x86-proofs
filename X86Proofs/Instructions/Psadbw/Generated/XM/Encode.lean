import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodePsadbwXmmM128 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  0x66 :: encodeSseMem 0xF6 dst am

end X86Proofs
