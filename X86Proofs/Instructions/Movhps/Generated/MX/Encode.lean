import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeMovhpsM64Xmm (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  encodeSseMem 0x17 src am

end X86Proofs
