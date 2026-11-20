import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeMovdM32Xmm (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  0x66 :: encodeSseMem 0x7E src am

end X86Proofs
