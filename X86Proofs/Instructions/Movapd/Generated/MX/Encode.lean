import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeMovapdM128Xmm (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  0x66 :: encodeSseMem 0x29 src am

end X86Proofs
