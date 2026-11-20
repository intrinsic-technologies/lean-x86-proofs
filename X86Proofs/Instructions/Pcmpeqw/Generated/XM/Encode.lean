import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodePcmpeqwXmmM128 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  0x66 :: encodeSseMem 0x75 dst am

end X86Proofs
