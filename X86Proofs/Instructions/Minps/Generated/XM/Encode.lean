import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeMinpsXmmM128 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  encodeSseMem 0x5D dst am

end X86Proofs
