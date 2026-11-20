import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeMovdqaM128Xmm (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  0x66 :: encodeSseMem 0x7F src am

end X86Proofs
