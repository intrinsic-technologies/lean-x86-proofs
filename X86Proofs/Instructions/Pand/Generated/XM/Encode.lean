import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodePandXmmM128 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  0x66 :: encodeSseMem 0xDB dst am

end X86Proofs
