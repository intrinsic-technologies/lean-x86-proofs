import X86Proofs.Step.FetchImm

namespace X86Proofs

def encodeMovRaxMoffs64 (moffs : BitVec 64) : List UInt8 :=
  0x48 :: 0xA1 :: immBytes 64 moffs

def encodeMovEaxMoffs32 (moffs : BitVec 64) : List UInt8 :=
  0xA1 :: immBytes 64 moffs

def encodeMovAxMoffs16 (moffs : BitVec 64) : List UInt8 :=
  0x66 :: 0xA1 :: immBytes 64 moffs

def encodeMovAlMoffs8 (moffs : BitVec 64) : List UInt8 :=
  0xA0 :: immBytes 64 moffs

def encodeMovRaxMoffs64A32 (moffs : BitVec 32) : List UInt8 :=
  0x67 :: 0x48 :: 0xA1 :: immBytes 32 moffs

def encodeMovEaxMoffs32A32 (moffs : BitVec 32) : List UInt8 :=
  0x67 :: 0xA1 :: immBytes 32 moffs

def encodeMovAxMoffs16A32 (moffs : BitVec 32) : List UInt8 :=
  0x67 :: 0x66 :: 0xA1 :: immBytes 32 moffs

def encodeMovAlMoffs8A32 (moffs : BitVec 32) : List UInt8 :=
  0x67 :: 0xA0 :: immBytes 32 moffs

end X86Proofs
