import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodePsubusbXmmM128 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  0x66 :: encodeSseMem 0xD8 dst am

end X86Proofs
