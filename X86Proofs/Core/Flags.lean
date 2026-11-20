import X86
import X86Proofs.Core.Runtime

/-!
# Status flags

The six status flags (Intel SDM Vol. 1 §3.4.3.1) as a pure record, `StatusFlags`; how they are
stored in RFLAGS (`StatusFlags.store`, which changes only the bits `statusFlagBits`) and read back
(`StatusFlags.ofRFLAGS`); and RFLAGS with those bits cleared (`clearStatusFlags`).

lean-x86's `X86.UserProcess.Flags` is a different record: it also has DF, and its
`packFlags`/`unpackFlags` convert a whole RFLAGS value (`packFlags` clears every other bit), so
`StatusFlags.store`, which keeps the other bits, is not stated through them.
-/

namespace X86Proofs

open X86

/-- The six status flags an arithmetic or logic instruction may write. -/
structure StatusFlags where
  /-- Carry (RFLAGS bit 0). -/
  CF : Bool
  /-- Parity of the low result byte (bit 2). -/
  PF : Bool
  /-- Auxiliary carry out of bit 3 (bit 4). -/
  AF : Bool
  /-- Zero (bit 6). -/
  ZF : Bool
  /-- Sign (bit 7). -/
  SF : Bool
  /-- Signed overflow (bit 11). -/
  OF : Bool
  deriving DecidableEq, Repr

/-- The RFLAGS bits of the six status flags: CF, PF, AF, ZF, SF, OF. -/
def statusFlagBits : List Nat := [0, 2, 4, 6, 7, 11]

/-- Even parity: an even number of set bits, as x86's PF reports it for the low result byte. -/
def evenParity (b : BitVec 8) : Bool :=
  !(b.getLsbD 0 ^^ b.getLsbD 1 ^^ b.getLsbD 2 ^^ b.getLsbD 3 ^^
    b.getLsbD 4 ^^ b.getLsbD 5 ^^ b.getLsbD 6 ^^ b.getLsbD 7)

/--
Store `f` into `rflags`, leaving every other bit unchanged. Bits are written in the order
OF, SF, ZF, AF, PF, CF, which is the order lean-x86's logic operations use.
-/
def StatusFlags.store (f : StatusFlags) (rflags : BitVec 64) : BitVec 64 :=
  let r := X86.Runtime.setSlice rflags 11 1 (BitVec.ofBool f.OF)
  let r := X86.Runtime.setSlice r 7 1 (BitVec.ofBool f.SF)
  let r := X86.Runtime.setSlice r 6 1 (BitVec.ofBool f.ZF)
  let r := X86.Runtime.setSlice r 4 1 (BitVec.ofBool f.AF)
  let r := X86.Runtime.setSlice r 2 1 (BitVec.ofBool f.PF)
  X86.Runtime.setSlice r 0 1 (BitVec.ofBool f.CF)

/-- `s` with its status flags set to `f`. -/
def setFlags {σ : Type} (s : X86.State σ) (f : StatusFlags) : X86.State σ :=
  { s with RFLAGS := f.store s.RFLAGS }

/-- Setting one bit at `lo` leaves every other bit unchanged. -/
theorem getLsbD_setSlice_one {w : Nat} (r : BitVec w) (lo j : Nat) (v : BitVec 1) (hj : j ≠ lo) :
    (X86.Runtime.setSlice r lo 1 v).getLsbD j = r.getLsbD j := by
  by_cases hw : j < w
  · rw [getLsbD_setSlice r lo 1 v j hw]
    simp [show ¬(lo ≤ j ∧ j < lo + 1) by omega]
  · rw [BitVec.getLsbD_of_ge r j (by omega),
      BitVec.getLsbD_of_ge (X86.Runtime.setSlice r lo 1 v) j (by omega)]

/-- Setting one bit at `lo` sets that bit. -/
theorem getLsbD_setSlice_one_self {w : Nat} (r : BitVec w) (lo : Nat) (v : BitVec 1)
    (hlo : lo < w) : (X86.Runtime.setSlice r lo 1 v).getLsbD lo = v.getLsbD 0 := by
  rw [getLsbD_setSlice r lo 1 v lo hlo]
  simp

/-- `StatusFlags.store` changes only the six status-flag bits (`statusFlagBits`). -/
theorem StatusFlags.getLsbD_store (f : StatusFlags) (r : BitVec 64) (j : Nat)
    (hj : j ∉ statusFlagBits) : (f.store r).getLsbD j = r.getLsbD j := by
  simp only [statusFlagBits, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  simp only [StatusFlags.store, getLsbD_setSlice_one _ _ _ _ hj.1, getLsbD_setSlice_one _ _ _ _ hj.2.1,
    getLsbD_setSlice_one _ _ _ _ hj.2.2.1, getLsbD_setSlice_one _ _ _ _ hj.2.2.2.1,
    getLsbD_setSlice_one _ _ _ _ hj.2.2.2.2.1, getLsbD_setSlice_one _ _ _ _ hj.2.2.2.2.2]

theorem StatusFlags.extractLsb'_store (f : StatusFlags) (r : BitVec 64) (j : Nat)
    (hj : j ∉ statusFlagBits) :
    (f.store r).extractLsb' j 1 = r.extractLsb' j 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have : i = 0 := by omega
  subst this
  simp only [BitVec.getLsbD_extractLsb', Nat.add_zero, StatusFlags.getLsbD_store f r j hj]

/-- RFLAGS with the six status-flag bits (`statusFlagBits`) cleared. -/
def clearStatusFlags (r : BitVec 64) : BitVec 64 := r &&& ~~~0x8D5#64

/-- Storing status flags does not change the other bits of RFLAGS. -/
theorem clearStatusFlags_store (f : StatusFlags) (r : BitVec 64) :
    clearStatusFlags (f.store r) = clearStatusFlags r := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [clearStatusFlags, clearStatusFlags, BitVec.getLsbD_and, BitVec.getLsbD_and]
  by_cases hs : j ∈ statusFlagBits
  · have : (~~~0x8D5#64).getLsbD j = false := by
      simp only [statusFlagBits, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [this, Bool.and_false, Bool.and_false]
  · rw [StatusFlags.getLsbD_store f r j hs]

/-- Setting a bit to the value it already has changes nothing. -/
theorem setSlice_one_getLsbD {w : Nat} (r : BitVec w) (lo : Nat) (hlo : lo < w) :
    X86.Runtime.setSlice r lo 1 (BitVec.ofBool (r.getLsbD lo)) = r := by
  apply BitVec.eq_of_getLsbD_eq
  intro j _
  by_cases hj : j = lo
  · subst hj
    rw [getLsbD_setSlice_one_self _ _ _ hlo]
    simp
  · exact getLsbD_setSlice_one _ _ _ _ hj

/--
Storing flags whose CF is the CF already in `r` writes only OF, SF, ZF, AF and PF, in that order,
as lean-x86's INC and DEC do (they leave CF alone).
-/
theorem StatusFlags.store_of_cf_eq (f : StatusFlags) (r : BitVec 64) (h : f.CF = r.getLsbD 0) :
    f.store r =
      (let r := X86.Runtime.setSlice r 11 1 (BitVec.ofBool f.OF)
       let r := X86.Runtime.setSlice r 7 1 (BitVec.ofBool f.SF)
       let r := X86.Runtime.setSlice r 6 1 (BitVec.ofBool f.ZF)
       let r := X86.Runtime.setSlice r 4 1 (BitVec.ofBool f.AF)
       X86.Runtime.setSlice r 2 1 (BitVec.ofBool f.PF)) := by
  simp only [StatusFlags.store, h]
  generalize hr' : X86.Runtime.setSlice (X86.Runtime.setSlice (X86.Runtime.setSlice
    (X86.Runtime.setSlice (X86.Runtime.setSlice r 11 1 (BitVec.ofBool f.OF)) 7 1
      (BitVec.ofBool f.SF)) 6 1 (BitVec.ofBool f.ZF)) 4 1 (BitVec.ofBool f.AF)) 2 1
        (BitVec.ofBool f.PF) = r'
  have h0 : r'.getLsbD 0 = r.getLsbD 0 := by
    subst hr'
    simp (disch := decide) only [getLsbD_setSlice_one]
  rw [← h0, setSlice_one_getLsbD _ 0 (by decide)]

/-- The six status flags held in `r` (bits 0, 2, 4, 6, 7, 11). -/
def StatusFlags.ofRFLAGS (r : BitVec 64) : StatusFlags :=
  ⟨r.getLsbD 0, r.getLsbD 2, r.getLsbD 4, r.getLsbD 6, r.getLsbD 7, r.getLsbD 11⟩

/-- Reading back stored flags gives the flags. -/
@[simp] theorem StatusFlags.ofRFLAGS_store (f : StatusFlags) (r : BitVec 64) :
    StatusFlags.ofRFLAGS (f.store r) = f := by
  cases f
  simp (disch := decide) only [StatusFlags.ofRFLAGS, StatusFlags.store, getLsbD_setSlice_one,
    getLsbD_setSlice_one_self, BitVec.getLsbD_ofBool]
  simp

/-- Storing the flags `r` already holds changes nothing. -/
@[simp] theorem StatusFlags.store_ofRFLAGS (r : BitVec 64) : (StatusFlags.ofRFLAGS r).store r = r := by
  simp (disch := decide) only [StatusFlags.store, StatusFlags.ofRFLAGS, setSlice_one_getLsbD]

/-- Storing the flags `r` holds with CF replaced by `c` sets only RFLAGS bit 0, as lean-x86's
`RFLAGS.setCF c` does (CLC, STC, CMC). -/
theorem StatusFlags.store_setCF (r : BitVec 64) (c : Bool) :
    { StatusFlags.ofRFLAGS r with CF := c }.store r =
      X86.Runtime.setSlice r 0 1 (BitVec.ofBool c) := by
  simp (disch := decide) only [StatusFlags.store, StatusFlags.ofRFLAGS, setSlice_one_getLsbD]

/-- Setting the status flags to the ones `s` already holds changes nothing. -/
@[simp] theorem setFlags_ofRFLAGS {σ : Type} (s : X86.State σ) :
    setFlags s (StatusFlags.ofRFLAGS s.RFLAGS) = s := by
  simp [setFlags]

/-! ### The direction flag

DF (RFLAGS bit 10) is not a status flag: CLD, STD and POPF write it, and the string instructions
read it to choose their direction. `dfBit` reads it; lean-x86's `RFLAGS.setDF v` is
`setSlice r 10 1 v`. -/

/-- The direction flag, RFLAGS bit 10, as lean-x86's `RFLAGS_Type.DF` reads it. -/
def dfBit (r : BitVec 64) : BitVec 1 := r.extractLsb' 10 1

/-- The direction flag (RFLAGS bit 10) is clear. -/
def DirectionFlagClear (r : BitVec 64) : Prop := dfBit r = 0

/-- The direction flag (RFLAGS bit 10) is set: the string instructions step their addresses down
(the `_down` forms of the string family). -/
def DirectionFlagSet (r : BitVec 64) : Prop := dfBit r = 1

/-- RFLAGS with the direction flag (bit 10) cleared. -/
def clearDirectionFlag (r : BitVec 64) : BitVec 64 := r &&& ~~~0x400#64

/-- Storing status flags keeps the direction flag. -/
@[simp] theorem dfBit_store (f : StatusFlags) (r : BitVec 64) : dfBit (f.store r) = dfBit r :=
  StatusFlags.extractLsb'_store f r 10 (by decide)

/-- Setting the direction flag sets it. -/
@[simp] theorem dfBit_setSlice_df (r : BitVec 64) (v : BitVec 1) :
    dfBit (X86.Runtime.setSlice r 10 1 v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have : i = 0 := by omega
  subst this
  simp only [dfBit, BitVec.getLsbD_extractLsb', Nat.add_zero]
  rw [getLsbD_setSlice_one_self _ _ _ (by decide)]
  simp

/-- Clearing the status flags keeps the direction flag. -/
@[simp] theorem dfBit_clearStatusFlags (r : BitVec 64) : dfBit (clearStatusFlags r) = dfBit r := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have : i = 0 := by omega
  subst this
  simp [dfBit, clearStatusFlags]

/-- Setting the direction flag changes no status flag. -/
@[simp] theorem StatusFlags.ofRFLAGS_setSlice_df (r : BitVec 64) (v : BitVec 1) :
    StatusFlags.ofRFLAGS (X86.Runtime.setSlice r 10 1 v) = StatusFlags.ofRFLAGS r := by
  simp (disch := decide) only [StatusFlags.ofRFLAGS, getLsbD_setSlice_one]

/-- Setting the direction flag changes no bit outside the status flags and DF. -/
@[simp] theorem clearDirectionFlag_clearStatusFlags_setSlice_df (r : BitVec 64) (v : BitVec 1) :
    clearDirectionFlag (clearStatusFlags (X86.Runtime.setSlice r 10 1 v)) =
      clearDirectionFlag (clearStatusFlags r) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [clearDirectionFlag, clearStatusFlags, BitVec.getLsbD_and]
  by_cases h : j = 10
  · subst h; simp
  · rw [getLsbD_setSlice_one _ _ _ _ h]

/-- Clearing the status flags commutes with setting the direction flag. -/
theorem clearStatusFlags_setSlice_df (r : BitVec 64) (v : BitVec 1) :
    clearStatusFlags (X86.Runtime.setSlice r 10 1 v) =
      X86.Runtime.setSlice (clearStatusFlags r) 10 1 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  by_cases h : j = 10
  · subst h
    simp only [clearStatusFlags, BitVec.getLsbD_and]
    rw [getLsbD_setSlice_one_self _ _ _ (by decide), getLsbD_setSlice_one_self _ _ _ (by decide)]
    simp
  · simp only [clearStatusFlags, BitVec.getLsbD_and]
    rw [getLsbD_setSlice_one _ _ _ _ h, getLsbD_setSlice_one _ _ _ _ h, BitVec.getLsbD_and]

/-- Clearing DF keeps every other bit. -/
theorem extractLsb'_clearDirectionFlag (r : BitVec 64) (j : Nat) (hj : j < 64) (hj10 : j ≠ 10) :
    (clearDirectionFlag r).extractLsb' j 1 = r.extractLsb' j 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have : i = 0 := by omega
  subst this
  have hb : (~~~0x400#64).getLsbD j = true :=
    (show ∀ k : Fin 64, k.val ≠ 10 → (~~~0x400#64).getLsbD k.val = true by decide) ⟨j, hj⟩ hj10
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', clearDirectionFlag,
    BitVec.getLsbD_and, Nat.add_zero, hb, Bool.and_true]

/-- Two values with the same bits outside DF and the same DF are equal. -/
theorem eq_of_clearDirectionFlag_eq {r r' : BitVec 64}
    (h : clearDirectionFlag r = clearDirectionFlag r') (hd : dfBit r = dfBit r') : r = r' := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  by_cases hj10 : j = 10
  · subst hj10
    have := congrArg (·.getLsbD 0) hd
    simpa [dfBit] using this
  · have := congrArg (·.getLsbD j) h
    have hb : (~~~0x400#64).getLsbD j = true :=
      (show ∀ k : Fin 64, k.val ≠ 10 → (~~~0x400#64).getLsbD k.val = true by decide) ⟨j, hj⟩
        hj10
    rw [clearDirectionFlag, clearDirectionFlag, BitVec.getLsbD_and, BitVec.getLsbD_and, hb,
      Bool.and_true, Bool.and_true] at this
    exact this

/-- RFLAGS values with the same status flags, the same DF and the same other bits are equal. -/
theorem rflags_eq_of {r r' : BitVec 64}
    (h : clearDirectionFlag (clearStatusFlags r) = clearDirectionFlag (clearStatusFlags r'))
    (hs : StatusFlags.ofRFLAGS r = StatusFlags.ofRFLAGS r') (hd : dfBit r = dfBit r') :
    r = r' := by
  have hc : clearStatusFlags r = clearStatusFlags r' :=
    eq_of_clearDirectionFlag_eq h (by simpa using hd)
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  by_cases hsj : j ∈ statusFlagBits
  · simp only [statusFlagBits, List.mem_cons, List.not_mem_nil, or_false] at hsj
    rcases hsj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact congrArg StatusFlags.CF hs
    · exact congrArg StatusFlags.PF hs
    · exact congrArg StatusFlags.AF hs
    · exact congrArg StatusFlags.ZF hs
    · exact congrArg StatusFlags.SF hs
    · exact congrArg StatusFlags.OF hs
  · have := congrArg (·.getLsbD j) hc
    have hb : (~~~0x8D5#64).getLsbD j = true :=
      (show ∀ k : Fin 64, k.val ∉ statusFlagBits → (~~~0x8D5#64).getLsbD k.val = true by
        decide) ⟨j, hj⟩ hsj
    rw [clearStatusFlags, clearStatusFlags, BitVec.getLsbD_and, BitVec.getLsbD_and, hb,
      Bool.and_true, Bool.and_true] at this
    exact this

/-- Clearing the status flags twice is clearing them once. -/
@[simp] theorem clearStatusFlags_clearStatusFlags (r : BitVec 64) :
    clearStatusFlags (clearStatusFlags r) = clearStatusFlags r := by
  simp [clearStatusFlags, BitVec.and_assoc]

/-- RFLAGS is its status flags stored into its other bits. -/
theorem StatusFlags.store_ofRFLAGS_clearStatusFlags (r : BitVec 64) :
    (StatusFlags.ofRFLAGS r).store (clearStatusFlags r) = r :=
  rflags_eq_of (by rw [clearStatusFlags_store, clearStatusFlags_clearStatusFlags])
    (StatusFlags.ofRFLAGS_store _ _) (by rw [dfBit_store, dfBit_clearStatusFlags])

section
open X86.Helpers

/-! Lemmas for proving lean-x86's flag computations (shared by the logic and arithmetic
operations). -/

theorem isParityEven8_run (b : BitVec 8) :
    Std.Bits.Is_Parity_Even (size := 8) b = .ok (evenParity b) := by
  have h : ∀ i : Fin 256, (Std.Bits.Is_Parity_Even (size := 8) (BitVec.ofNat 8 i.val)).toOption =
      some (evenParity (BitVec.ofNat 8 i.val)) := by decide +kernel
  have hb := h ⟨b.toNat, b.isLt⟩
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb
  cases he : Std.Bits.Is_Parity_Even (size := 8) b <;> simp_all [Except.toOption]

theorem ite_one_zero (p : Prop) [Decidable p] :
    (if p then 1#1 else 0#1) = BitVec.ofBool (decide p) := by
  by_cases h : p <;> simp [h]

theorem ofNat_one_ite (b : Bool) :
    BitVec.ofNat 1 (if b = true then 1 else 0) = BitVec.ofBool b := by
  cases b <;> rfl

theorem extractLsb'_msb {n : Nat} (r : BitVec n) (k : Nat) (hk : k + 1 = n) :
    r.extractLsb' k 1 = BitVec.ofBool r.msb := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have : i = 0 := by omega
  subst this
  simp [BitVec.msb_eq_getLsbD_last, ← hk]

theorem ite_zero_one (p : Prop) [Decidable p] :
    (if p then 0#1 else 1#1) = BitVec.ofBool (!decide p) := by
  by_cases h : p <;> simp [h]

/-- `RFLAGS.CF` returns CF (RFLAGS bit 0) as a one-bit value and leaves the state unchanged: the
carry-in that ADC and SBB read. -/
theorem rflagsCF_run {σ : Type} (s : X86.State σ) :
    (RFLAGS.CF : Runtime.SpecM Exception (X86.State σ) Runtime.Bit).run s =
      (.ok (BitVec.ofBool (StatusFlags.ofRFLAGS s.RFLAGS).CF), s) := by
  simp only [RFLAGS.CF, StatusFlags.ofRFLAGS, x86_runtime]
  show (Except.ok (BitVec.extractLsb' 0 1 s.RFLAGS), s) = _
  congr 2
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have : i = 0 := by omega
  subst this
  simp

/-- `RFLAGS.setCF v` sets RFLAGS bit 0 to `v`. -/
theorem rflagsSetCF_run {σ : Type} (s : X86.State σ) (v : BitVec 1) :
    (RFLAGS.setCF v : Runtime.SpecM Exception (X86.State σ) Unit).run s =
      (.ok (), { s with RFLAGS := X86.Runtime.setSlice s.RFLAGS 0 1 v }) := rfl

/-- `RFLAGS.DF` returns the direction flag (RFLAGS bit 10) and leaves the state unchanged. -/
theorem rflagsDF_run {σ : Type} (s : X86.State σ) :
    (RFLAGS.DF : Runtime.SpecM Exception (X86.State σ) Runtime.Bit).run s =
      (.ok (dfBit s.RFLAGS), s) := rfl

/-- `RFLAGS.setDF v` sets RFLAGS bit 10 to `v`. -/
theorem rflagsSetDF_run {σ : Type} (s : X86.State σ) (v : BitVec 1) :
    (RFLAGS.setDF v : Runtime.SpecM Exception (X86.State σ) Unit).run s =
      (.ok (), { s with RFLAGS := X86.Runtime.setSlice s.RFLAGS 10 1 v }) := rfl

/-- lean-x86's unsigned value of a one-bit flag is the flag as a number. -/
theorem unsigned_ofBool (c : Bool) : X86.Runtime.Unsigned (BitVec.ofBool c) = (c.toNat : Int) := by
  cases c <;> rfl

/-- ZF as lean-x86 computes it (`Is_Zero`, a `decide`) and as a spec writes it (`==`). -/
theorem beq_zero_eq_decide {n : Nat} (r : BitVec n) : (r == 0#n) = decide (r = 0#n) := by
  by_cases h : r = 0#n <;> simp [h]

end

end X86Proofs
