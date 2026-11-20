import X86Proofs.Program.ReadWrite.Rmw
import X86Proofs.Core.Bits

/-!
# Bit strings in memory: BT, BTS, BTR, BTC with a register bit offset

With a memory bit base and a register bit offset, BT, BTS, BTR and BTC address the operand that
holds the selected bit: the bit base's address plus `bitStringOffset` of the offset register
(`Core/Bits.lean`; the offset is signed and not reduced modulo the operand size). So the address
depends on a register besides the `AddrMode`'s own:

- `bitStringAddr n am src next s`: that address, `am.addr s next` plus `bitStringOffset` of the
  `n`-bit register `src` in `s`.
- `BitLoadPre p am n src codeLen` (BT: `LoadPre` there), `BitRmwPre p am n src codeLen` (BTS, BTR,
  BTC: `StorePre` there, a read-modify-write), with an instruction of `codeLen` bytes at `p`;
  `SegBitLoadPre`, `SegBitRmwPre` with a segment override `r` (FS or GS) of base `base` (the bytes
  at `base + bitStringAddr …`); `LockedBitRmwPre`, `SegLockedBitRmwPre` for the LOCK forms
  (`LockReady` at the operand).
- `bitLoad_facts`, `bitRmw_facts`, `segBitLoad_facts`, `segBitRmw_facts`, `lockedBitRmw_lock`,
  `segLockedBitRmw_lock`: their facts at the step theorems' address (`AddrMode.addrAt` plus the
  offset).
- At address size 32 (`67`): `bitStringAddr32` (the low 32 bits, zero-extended), `BitLoad32Pre`,
  `BitRmw32Pre`, `LockedBitRmw32Pre` and their facts `bitLoad32_facts`, `bitRmw32_facts`,
  `lockedBitRmw32_lock`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- The address of the `n`-bit operand holding the bit that register `src` selects in the bit
string at `[am]`, for an instruction ending at `next`: `am.addr s next` plus
`bitStringOffset` of the register. -/
def bitStringAddr (n : Nat) (am : AddrMode) (src : BitVec 5) (next : BitVec 64) (s : RamState) :
    BitVec 64 :=
  am.addr s next + bitStringOffset ((Operand.reg src : Operand n).read s)

/-- The precondition of BT on a bit string at `[am]` with offset register `src`, at operand size
`n`, by an instruction of `codeLen` bytes at `p`: RIP = `p` and the operand's `n / 8` bytes can be
read. -/
abbrev BitLoadPre (p : BitVec 64) (am : AddrMode) (n : Nat) (src : BitVec 5) (codeLen : Nat) :
    RamState → Prop :=
  LoadPre p (bitStringAddr n am src (p + BitVec.ofNat 64 codeLen)) (n / 8)

/-- The precondition of BTS, BTR or BTC on a bit string at `[am]` with offset register `src`, at
operand size `n`, by an instruction of `codeLen` bytes at `p`: `StorePre` of the operand's `n / 8`
bytes (a read-modify-write). -/
abbrev BitRmwPre (p : BitVec 64) (am : AddrMode) (n : Nat) (src : BitVec 5) (codeLen : Nat) :
    RamState → Prop :=
  StorePre p codeLen (bitStringAddr n am src (p + BitVec.ofNat 64 codeLen)) (n / 8)

/-- `BitLoadPre` with a segment override `r` (FS or GS) whose base is `base`. -/
abbrev SegBitLoadPre (p : BitVec 64) (r : SegReg) (base : BitVec 64) (am : AddrMode) (n : Nat)
    (src : BitVec 5) (codeLen : Nat) : RamState → Prop :=
  SegLoadPre p r base (bitStringAddr n am src (p + BitVec.ofNat 64 codeLen)) (n / 8)

/-- `BitRmwPre` with a segment override `r` (FS or GS) whose base is `base`. -/
abbrev SegBitRmwPre (p : BitVec 64) (r : SegReg) (base : BitVec 64) (am : AddrMode) (n : Nat)
    (src : BitVec 5) (codeLen : Nat) : RamState → Prop :=
  SegStorePre p codeLen r base (bitStringAddr n am src (p + BitVec.ofNat 64 codeLen)) (n / 8)

/-- The precondition of a LOCK-prefixed BTS, BTR or BTC on a bit string: `BitRmwPre`, and the
operand is ready to lock (`LockReady`). -/
structure LockedBitRmwPre [Bindings] (p : BitVec 64) (am : AddrMode) (n : Nat) (src : BitVec 5)
    (codeLen : Nat) (s : RamState) : Prop where
  rmw : BitRmwPre p am n src codeLen s
  lock : LockReady s (bitStringAddr n am src (p + BitVec.ofNat 64 codeLen) s) (n / 8)

/-- `LockedBitRmwPre` with a segment override `r` (FS or GS) whose base is `base`. -/
structure SegLockedBitRmwPre [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (n : Nat) (src : BitVec 5) (codeLen : Nat) (s : RamState) : Prop where
  rmw : SegBitRmwPre p r base am n src codeLen s
  lock : LockReady s (base + bitStringAddr n am src (p + BitVec.ofNat 64 codeLen) s) (n / 8)

/-- `BitLoadPre`'s facts at the step theorems' address. -/
theorem bitLoad_facts {p : BitVec 64} {am : AddrMode} {n : Nat} {src : BitVec 5} {codeLen : Nat}
    {s : RamState} (h : BitLoadPre p am n src codeLen s) :
    s.RIP = p ∧ MemReadable s (am.addrAt s codeLen +
      bitStringOffset ((Operand.reg src : Operand n).read s)) (n / 8) := by
  obtain ⟨hp, hr⟩ := h
  subst hp
  exact ⟨rfl, hr⟩

/-- `BitRmwPre`'s facts at the step theorems' address: the bytes are readable and apart from the
page tables. -/
theorem bitRmw_facts {p : BitVec 64} {am : AddrMode} {n : Nat} {src : BitVec 5} {codeLen : Nat}
    {s : RamState} (h : BitRmwPre p am n src codeLen s) :
    let a := am.addrAt s codeLen + bitStringOffset ((Operand.reg src : Operand n).read s)
    s.RIP = p ∧ MemReadable s a (n / 8) ∧ PageTableEntriesApart a.toNat (n / 8) := by
  obtain ⟨hp, hw, -⟩ := h
  subst hp
  exact ⟨rfl, hw.readable, hw.tables⟩

/-- `SegBitLoadPre`'s facts at the step theorems' address (`segBase` of the segment plus the
address). -/
theorem segBitLoad_facts {p base : BitVec 64} {r : SegReg} {am : AddrMode} {n : Nat}
    {src : BitVec 5} {codeLen : Nat} {s : RamState}
    (h : SegBitLoadPre p r base am n src codeLen s) :
    s.RIP = p ∧ SegReady (r.read s) ∧ segBase (r.read s) = base ∧
      MemReadable s (segBase (r.read s) + (am.addrAt s codeLen +
        bitStringOffset ((Operand.reg src : Operand n).read s))) (n / 8) := by
  obtain ⟨hp, ⟨hseg, hbase⟩, hr⟩ := h
  subst hp hbase
  exact ⟨rfl, hseg, rfl, hr⟩

/-- `SegBitRmwPre`'s facts at the step theorems' address (`segBase` of the segment plus the
address). -/
theorem segBitRmw_facts {p base : BitVec 64} {r : SegReg} {am : AddrMode} {n : Nat}
    {src : BitVec 5} {codeLen : Nat} {s : RamState} (h : SegBitRmwPre p r base am n src codeLen s) :
    let a := segBase (r.read s) + (am.addrAt s codeLen +
      bitStringOffset ((Operand.reg src : Operand n).read s))
    s.RIP = p ∧ SegReady (r.read s) ∧ segBase (r.read s) = base ∧ MemReadable s a (n / 8) ∧
      PageTableEntriesApart a.toNat (n / 8) := by
  obtain ⟨⟨hp, hw, -⟩, ⟨hseg, hbase⟩⟩ := h
  subst hp hbase
  exact ⟨rfl, hseg, rfl, hw.readable, hw.tables⟩

/-- `LockedBitRmwPre`'s lock facts at the step theorems' address. -/
theorem lockedBitRmw_lock [Bindings] {p : BitVec 64} {am : AddrMode} {n : Nat} {src : BitVec 5}
    {codeLen : Nat} {s : RamState} (h : LockedBitRmwPre p am n src codeLen s) :
    LockReady s (am.addrAt s codeLen + bitStringOffset ((Operand.reg src : Operand n).read s))
      (n / 8) := by
  obtain ⟨⟨hp, -, -⟩, hl⟩ := h
  subst hp
  exact hl

/-- `SegLockedBitRmwPre`'s lock facts at the step theorems' address. -/
theorem segLockedBitRmw_lock [Bindings] {p base : BitVec 64} {r : SegReg} {am : AddrMode}
    {n : Nat} {src : BitVec 5} {codeLen : Nat} {s : RamState}
    (h : SegLockedBitRmwPre p r base am n src codeLen s) :
    LockReady s (segBase (r.read s) + (am.addrAt s codeLen +
      bitStringOffset ((Operand.reg src : Operand n).read s))) (n / 8) := by
  obtain ⟨⟨⟨hp, -, -⟩, -, hbase⟩, hl⟩ := h
  subst hp hbase
  exact hl

/-! ### Address size 32 (`67`)

Behind an address-size prefix lean-x86 adds the offset to the bit base's offset before keeping the
low 32 bits (`handleRIPRelativeAddress_addrMode32_add_run`), so the operand is at
`bitStringAddr32`: `bitStringAddr`'s low 32 bits, zero-extended. -/

/-- The address of the operand `bitStringAddr` selects, at address size 32: its low 32 bits,
zero-extended (the 32-bit sum of the bit base's address and the offset). -/
def bitStringAddr32 (n : Nat) (am : AddrMode) (src : BitVec 5) (next : BitVec 64) (s : RamState) :
    BitVec 64 :=
  ((bitStringAddr n am src next s).setWidth 32).setWidth 64

/-- `BitLoadPre` at address size 32 (the operand at `bitStringAddr32`). -/
abbrev BitLoad32Pre (p : BitVec 64) (am : AddrMode) (n : Nat) (src : BitVec 5) (codeLen : Nat) :
    RamState → Prop :=
  LoadPre p (bitStringAddr32 n am src (p + BitVec.ofNat 64 codeLen)) (n / 8)

/-- `BitRmwPre` at address size 32 (the operand at `bitStringAddr32`). -/
abbrev BitRmw32Pre (p : BitVec 64) (am : AddrMode) (n : Nat) (src : BitVec 5) (codeLen : Nat) :
    RamState → Prop :=
  StorePre p codeLen (bitStringAddr32 n am src (p + BitVec.ofNat 64 codeLen)) (n / 8)

/-- `LockedBitRmwPre` at address size 32: `BitRmw32Pre`, and the operand is ready to lock. -/
structure LockedBitRmw32Pre [Bindings] (p : BitVec 64) (am : AddrMode) (n : Nat) (src : BitVec 5)
    (codeLen : Nat) (s : RamState) : Prop where
  rmw : BitRmw32Pre p am n src codeLen s
  lock : LockReady s (bitStringAddr32 n am src (p + BitVec.ofNat 64 codeLen) s) (n / 8)

/-- `BitLoad32Pre`'s facts at the step theorems' address. -/
theorem bitLoad32_facts {p : BitVec 64} {am : AddrMode} {n : Nat} {src : BitVec 5}
    {codeLen : Nat} {s : RamState} (h : BitLoad32Pre p am n src codeLen s) :
    s.RIP = p ∧ MemReadable s (((am.addrAt s codeLen +
      bitStringOffset ((Operand.reg src : Operand n).read s)).setWidth 32).setWidth 64) (n / 8) := by
  obtain ⟨hp, hr⟩ := h
  subst hp
  exact ⟨rfl, hr⟩

/-- `BitRmw32Pre`'s facts at the step theorems' address: the bytes are readable and apart from the
page tables. -/
theorem bitRmw32_facts {p : BitVec 64} {am : AddrMode} {n : Nat} {src : BitVec 5}
    {codeLen : Nat} {s : RamState} (h : BitRmw32Pre p am n src codeLen s) :
    let a := ((am.addrAt s codeLen +
      bitStringOffset ((Operand.reg src : Operand n).read s)).setWidth 32).setWidth 64
    s.RIP = p ∧ MemReadable s a (n / 8) ∧ PageTableEntriesApart a.toNat (n / 8) := by
  obtain ⟨hp, hw, -⟩ := h
  subst hp
  exact ⟨rfl, hw.readable, hw.tables⟩

/-- `LockedBitRmw32Pre`'s lock facts at the step theorems' address. -/
theorem lockedBitRmw32_lock [Bindings] {p : BitVec 64} {am : AddrMode} {n : Nat}
    {src : BitVec 5} {codeLen : Nat} {s : RamState} (h : LockedBitRmw32Pre p am n src codeLen s) :
    LockReady s (((am.addrAt s codeLen +
      bitStringOffset ((Operand.reg src : Operand n).read s)).setWidth 32).setWidth 64) (n / 8) := by
  obtain ⟨⟨hp, -, -⟩, hl⟩ := h
  subst hp
  exact hl

/-! ### Preconditions after a block -/

section Carry

variable {e : Effect} {s s' : RamState}

attribute [x86_addr] bitStringAddr bitStringAddr32

theorem bitStringAddr_obs (n : Nat) (am : AddrMode) (src : BitVec 5) (next : BitVec 64) :
    AddrObs (bitStringAddr n am src next) := by
  intro t t' hob
  simp only [bitStringAddr, AddrMode.addr_obs hob, hob.read_reg]

theorem bitStringAddr32_obs (n : Nat) (am : AddrMode) (src : BitVec 5) (next : BitVec 64) :
    AddrObs (bitStringAddr32 n am src next) := by
  intro t t' hob
  simp only [bitStringAddr32, bitStringAddr, AddrMode.addr_obs hob, hob.read_reg]

@[x86_pre] theorem LockedBitRmwPre.of_holds [Bindings] (h : e.Holds s s')
    (ho : Obs (e.after s true) s') {p : BitVec 64} {am : AddrMode} {n : Nat} {src : BitVec 5}
    {codeLen : Nat} (hrmw : BitRmwPre p am n src codeLen s')
    (hl : LockReady s (bitStringAddr n am src (p + BitVec.ofNat 64 codeLen) (e.after s true))
      (n / 8)) :
    LockedBitRmwPre p am n src codeLen s' :=
  ⟨hrmw, by rw [(bitStringAddr_obs n am src _).eq ho]; exact h.lockReady_iff.mpr hl⟩

@[x86_pre] theorem SegLockedBitRmwPre.of_holds [Bindings] (h : e.Holds s s')
    (ho : Obs (e.after s true) s') {p base : BitVec 64} {r : SegReg} {am : AddrMode} {n : Nat}
    {src : BitVec 5} {codeLen : Nat} (hrmw : SegBitRmwPre p r base am n src codeLen s')
    (hl : LockReady s
      (base + bitStringAddr n am src (p + BitVec.ofNat 64 codeLen) (e.after s true)) (n / 8)) :
    SegLockedBitRmwPre p r base am n src codeLen s' :=
  ⟨hrmw, by rw [(bitStringAddr_obs n am src _).eq ho]; exact h.lockReady_iff.mpr hl⟩

@[x86_pre] theorem LockedBitRmw32Pre.of_holds [Bindings] (h : e.Holds s s')
    (ho : Obs (e.after s true) s') {p : BitVec 64} {am : AddrMode} {n : Nat} {src : BitVec 5}
    {codeLen : Nat} (hrmw : BitRmw32Pre p am n src codeLen s')
    (hl : LockReady s (bitStringAddr32 n am src (p + BitVec.ofNat 64 codeLen) (e.after s true))
      (n / 8)) :
    LockedBitRmw32Pre p am n src codeLen s' :=
  ⟨hrmw, by rw [(bitStringAddr32_obs n am src _).eq ho]; exact h.lockReady_iff.mpr hl⟩

end Carry

end X86Proofs
