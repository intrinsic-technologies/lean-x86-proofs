import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeDivpsXmmM128 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  encodeSseMem 0x5E dst am

end X86Proofs
