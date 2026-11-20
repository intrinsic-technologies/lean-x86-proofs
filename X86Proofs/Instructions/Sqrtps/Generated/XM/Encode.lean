import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeSqrtpsXmmM128 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  encodeSseMem 0x51 dst am

end X86Proofs
