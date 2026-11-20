import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeMovsdM64Xmm (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF2 :: encodeSseMem 0x11 src am

end X86Proofs
