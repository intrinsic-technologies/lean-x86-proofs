import X86Proofs.Core.Fpu
import X86Proofs.Core.Oracle
import X86Proofs.Core.Run
import X86Proofs.Core.Float

namespace X86Proofs

open X86 X86.Helpers X86.Runtime

/-- The class of an 80-bit value, as lean-x86's `FP87.Classify` computes it: the exponent
(bits 64–78) all ones is an infinity (integer bit 63 set, fraction zero), a quiet NaN (fraction
bit 62 set) or a signalling NaN, or unsupported (integer bit clear); the exponent zero is a zero
(integer bit and fraction clear) or a denormal; otherwise normal with the integer bit set, else
unsupported. -/
def fp87Class (x : BitVec 80) : FP87_Class_Type :=
  if x.extractLsb' 64 15 = 0x7FFF then
    if x.extractLsb' 63 1 = 1 then
      if x.extractLsb' 0 63 = 0 then .FP87_Class_Infinity
      else if x.extractLsb' 62 1 = 1 then .FP87_Class_QNaN else .FP87_Class_SNaN
    else .FP87_Class_Unsupported
  else if x.extractLsb' 64 15 = 0 then
    if x.extractLsb' 63 1 = 0 then
      if x.extractLsb' 0 63 = 0 then .FP87_Class_Zero else .FP87_Class_Denormal
    else .FP87_Class_Denormal
  else if x.extractLsb' 63 1 = 1 then .FP87_Class_Normal else .FP87_Class_Unsupported

theorem classify_eq (x : BitVec 80) : FP87.Classify x = .ok (fp87Class x) := by
  unfold FP87.Classify fp87Class
  simp only [x86_runtime, f80Mantissa_eq, F80_Type.Exponent, X86.Helpers.Std.Bits.Is_All_Ones,
    bind, pure, Except.bind, Except.pure]
  have h1 : BitVec.extractLsb' 63 1 (BitVec.extractLsb' 0 64 x) = BitVec.extractLsb' 63 1 x := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [BitVec.getLsbD_extractLsb']
  have h2 : BitVec.extractLsb' 0 63 (BitVec.extractLsb' 0 64 x) = BitVec.extractLsb' 0 63 x := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [BitVec.getLsbD_extractLsb']
  have h3 : BitVec.extractLsb' 62 1 (BitVec.extractLsb' 0 63 x) = BitVec.extractLsb' 62 1 x := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [BitVec.getLsbD_extractLsb']
  simp only [h1, h2, h3, beq_iff_eq, show BitVec.allOnes 15 = 32767#15 from rfl]
  generalize BitVec.extractLsb' 64 15 x = e
  generalize BitVec.extractLsb' 63 1 x = j
  generalize BitVec.extractLsb' 62 1 x = q
  generalize BitVec.extractLsb' 0 63 x = f
  have hj : ∀ j : BitVec 1, j = 0 ∨ j = 1 := by decide
  rcases hj j with rfl | rfl <;> rcases hj q with rfl | rfl <;>
    by_cases he : e = 32767 <;> by_cases he0 : e = 0 <;> by_cases hf : f = 0 <;> simp_all

/-- The tag lean-x86 gives a value written to the register stack (`FP87.Get_Tag_Word_Value`): 0
for a normal value, 1 for a zero, 2 (special) for anything else. -/
def x87Tag (v : BitVec 80) : BitVec 2 :=
  match fp87Class v with
  | .FP87_Class_Normal => 0
  | .FP87_Class_Zero => 1
  | _ => 2

theorem getTagWordValue_eq (v : BitVec 80) : FP87.Get_Tag_Word_Value v = .ok (x87Tag v) := by
  unfold FP87.Get_Tag_Word_Value x87Tag
  rw [classify_eq]
  cases fp87Class v <;> rfl

/-- A status word with the exception flags `f` ORed into its sticky flags (bits 0–5). -/
def fswOrFlags (fsw : BitVec 16) (f : BitVec 6) : BitVec 16 :=
  setSlice fsw 0 6 (fsw.extractLsb' 0 6 ||| f)

/-- A status word with its condition codes set one by one as lean-x86 sets them (`setC0`, `setC1`,
`setC2`, `setC3`, in that order). -/
def fswSetC (fsw : BitVec 16) (c0 c1 c2 c3 : BitVec 1) : BitVec 16 :=
  setSlice (setSlice (setSlice (setSlice fsw 8 1 c0) 9 1 c1) 10 1 c2) 14 1 c3

/-- The `j`-th oracle bit after `o`'s position, as a one-bit value (`UNSPECIFIED (size := 1)`). -/
def oBit (o : X86.Runtime.Oracle) (j : Nat) : BitVec 1 := BitVec.ofBool (oracleBit (oracleSkip o j))

/-- The value with its sign bit (79) replaced by `b`. -/
def fprSetSign (x : BitVec 80) (b : BitVec 1) : BitVec 80 := setSlice x 79 1 b

/-- The sign bit (79) of an 80-bit value. -/
def fprSign (x : BitVec 80) : BitVec 1 := x.extractLsb' 79 1

/-- Every x87 exception is masked: the control word's IM, DM, ZM, OM, UM and PM (bits 0–5) are
set. -/
def FcwMasked (fcw : BitVec 16) : Prop := fcw.extractLsb' 0 6 = 63

/-- The register file with physical register R`r` set to `v`. -/
def fprSet (fp : X86.Runtime.Array 8 F80_Type) (r : BitVec 3) (v : BitVec 80) :
    X86.Runtime.Array 8 F80_Type :=
  Vector.set fp (fprIndex r) v

@[simp] theorem fprSet_get_self (fp : X86.Runtime.Array 8 F80_Type) (r : BitVec 3)
    (v : BitVec 80) : (fprSet fp r v)[fprIndex r] = v := by
  simp [fprSet]

theorem sub_one_ne3 (x : BitVec 3) : x - 1 ≠ x := by
  revert x
  decide

theorem fprSet_get_of_ne (fp : X86.Runtime.Array 8 F80_Type) {r r' : BitVec 3} (h : r ≠ r')
    (v : BitVec 80) : (fprSet fp r v)[fprIndex r'] = fp[fprIndex r'] := by
  have hi : (fprIndex r).val ≠ (fprIndex r').val := fun e => h (BitVec.eq_of_toNat_eq e)
  simp [fprSet, hi]

theorem fprSet_ite_get_self (c : Prop) [Decidable c] (fp : X86.Runtime.Array 8 F80_Type)
    (r : BitVec 3) (v : BitVec 80) :
    (if c then fp else fprSet fp r v)[fprIndex r] = if c then fp[fprIndex r] else v := by
  split
  · rfl
  · exact fprSet_get_self _ _ _

theorem fprSet_ite_get_of_ne (c : Prop) [Decidable c] (fp : X86.Runtime.Array 8 F80_Type)
    {r r' : BitVec 3} (h : r ≠ r') (v : BitVec 80) :
    (if c then fp else fprSet fp r v)[fprIndex r'] = fp[fprIndex r'] := by
  split
  · rfl
  · exact fprSet_get_of_ne _ h _

theorem fprSet2_ite_get_hi (c : Prop) [Decidable c] (fp : X86.Runtime.Array 8 F80_Type)
    (r : BitVec 3) (v w : BitVec 80) :
    (if c then fp else fprSet (fprSet fp r v) (r - 1) w)[fprIndex r] =
      if c then fp[fprIndex r] else v := by
  split
  · rfl
  · rw [fprSet_get_of_ne _ (sub_one_ne3 r), fprSet_get_self]

theorem fprSet2_ite_get_lo (c : Prop) [Decidable c] (fp : X86.Runtime.Array 8 F80_Type)
    (r : BitVec 3) (v w : BitVec 80) :
    (if c then fp else fprSet (fprSet fp r v) (r - 1) w)[fprIndex (r - 1)] =
      if c then fp[fprIndex (r - 1)] else w := by
  split
  · rfl
  · exact fprSet_get_self _ _ _

theorem fprSet2_ite_get_of_ne (c : Prop) [Decidable c] (fp : X86.Runtime.Array 8 F80_Type)
    {r r' : BitVec 3} (h1 : r ≠ r') (h2 : r - 1 ≠ r') (v w : BitVec 80) :
    (if c then fp else fprSet (fprSet fp r v) (r - 1) w)[fprIndex r'] = fp[fprIndex r'] := by
  split
  · rfl
  · rw [fprSet_get_of_ne _ h2, fprSet_get_of_ne _ h1]

/-- The rounding control RC of a control word (bits 10–11). -/
def fcwRC (fcw : BitVec 16) : BitVec 2 := fcw.extractLsb' 10 2

/-- The stack top TOP of a status word (bits 11–13). -/
def fswTop (fsw : BitVec 16) : BitVec 3 := fsw.extractLsb' 11 3

/-- A status word with TOP set to `top`. -/
def fswSetTop (fsw : BitVec 16) (top : BitVec 3) : BitVec 16 := setSlice fsw 11 3 top

/-- The tag of physical register R`r` in a tag word (bits `2r`, `2r + 1`): 0 valid, 1 zero,
2 special, 3 empty. -/
def ftwTag (ftw : BitVec 16) (r : BitVec 3) : BitVec 2 := ftw.extractLsb' (r.toNat * 2) 2

/-- A tag word with the tag of R`r` set to `tag`. -/
def ftwSet (ftw : BitVec 16) (r : BitVec 3) (tag : BitVec 2) : BitVec 16 :=
  setSlice ftw (r.toNat * 2) 2 tag

@[simp] theorem ftwTag_ftwSet_self (f : BitVec 16) (r : BitVec 3) (v : BitVec 2) :
    ftwTag (ftwSet f r v) r = v := by
  have hr := r.isLt
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ftwTag, ftwSet, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [getLsbD_setSlice _ _ _ _ _ (by omega)]
  split
  · exact congrArg _ (by omega)
  · omega

theorem ftwTag_ftwSet_of_ne (f : BitVec 16) {r r' : BitVec 3} (h : r ≠ r') (v : BitVec 2) :
    ftwTag (ftwSet f r v) r' = ftwTag f r' := by
  have hr := r.isLt
  have hr' := r'.isLt
  have hne : r.toNat ≠ r'.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ftwTag, ftwSet, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [getLsbD_setSlice _ _ _ _ _ (by omega)]
  split
  · omega
  · rfl

@[simp] theorem ftwSet_ftwSet_self (f : BitVec 16) (r : BitVec 3) (a b : BitVec 2) :
    ftwSet (ftwSet f r a) r b = ftwSet f r b := by
  have hr := r.isLt
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ftwSet]
  rw [getLsbD_setSlice _ _ _ _ _ hi, getLsbD_setSlice _ _ _ _ _ hi, getLsbD_setSlice _ _ _ _ _ hi]
  split <;> rfl

/-- Tags of different registers set in either order. -/
theorem ftwSet_comm (f : BitVec 16) {r r' : BitVec 3} (h : r ≠ r') (a b : BitVec 2) :
    ftwSet (ftwSet f r a) r' b = ftwSet (ftwSet f r' b) r a := by
  have hr := r.isLt
  have hr' := r'.isLt
  have hne : r.toNat ≠ r'.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ftwSet]
  rw [getLsbD_setSlice _ _ _ _ _ hi, getLsbD_setSlice _ _ _ _ _ hi, getLsbD_setSlice _ _ _ _ _ hi,
    getLsbD_setSlice _ _ _ _ _ hi]
  split <;> split <;> first | rfl | omega

/-- Setting a register's tag to its value leaves the tag word alone. -/
theorem ftwSet_ftwTag (f : BitVec 16) (r : BitVec 3) : ftwSet f r (ftwTag f r) = f := by
  have hr := r.isLt
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ftwSet, ftwTag]
  rw [getLsbD_setSlice _ _ _ _ _ hi]
  split
  · simp only [BitVec.getLsbD_extractLsb']
    rw [decide_eq_true (by omega), Bool.true_and]
    exact congrArg _ (by omega)
  · rfl

/-- A value written to the register stack is never tagged empty. -/
theorem x87Tag_ne_three (v : BitVec 80) : x87Tag v ≠ 3 := by
  unfold x87Tag
  split <;> decide

/-! ### Bits of the status word -/

theorem fswTop_setSlice (f : BitVec 16) (lo w : Nat) (v : BitVec w)
    (h : lo + w ≤ 11 ∨ 14 ≤ lo) : fswTop (setSlice f lo w v) = fswTop f := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [fswTop, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [getLsbD_setSlice _ _ _ _ _ (by omega)]
  simp only [show ¬ (lo ≤ 11 + i ∧ 11 + i < lo + w) by omega, ite_false]

@[simp] theorem fswTop_fswSetTop (f : BitVec 16) (t : BitVec 3) : fswTop (fswSetTop f t) = t := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [fswTop, fswSetTop, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [getLsbD_setSlice _ _ _ _ _ (by omega)]
  simp only [show 11 ≤ 11 + i ∧ 11 + i < 11 + 3 by omega, and_self, ite_true]
  congr 1; omega

@[simp] theorem fswTop_fswOrFlags (f : BitVec 16) (x : BitVec 6) :
    fswTop (fswOrFlags f x) = fswTop f :=
  fswTop_setSlice _ _ _ _ (by omega)

@[simp] theorem fswTop_fswSetC (f : BitVec 16) (c0 c1 c2 c3 : BitVec 1) :
    fswTop (fswSetC f c0 c1 c2 c3) = fswTop f := by
  unfold fswSetC
  rw [fswTop_setSlice _ 14 1 _ (by omega), fswTop_setSlice _ 10 1 _ (by omega),
    fswTop_setSlice _ 9 1 _ (by omega), fswTop_setSlice _ 8 1 _ (by omega)]

theorem fswES_setSlice (f : BitVec 16) (lo w : Nat) (v : BitVec w)
    (h : lo + w ≤ 7 ∨ 8 ≤ lo) : fswES (setSlice f lo w v) = fswES f := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [fswES, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [getLsbD_setSlice _ _ _ _ _ (by omega)]
  simp only [show ¬ (lo ≤ 7 + i ∧ 7 + i < lo + w) by omega, ite_false]

@[simp] theorem fswES_fswSetTop (f : BitVec 16) (t : BitVec 3) :
    fswES (fswSetTop f t) = fswES f := fswES_setSlice _ _ _ _ (by omega)

@[simp] theorem fswES_fswOrFlags (f : BitVec 16) (x : BitVec 6) :
    fswES (fswOrFlags f x) = fswES f := fswES_setSlice _ _ _ _ (by omega)

@[simp] theorem fswES_fswSetC (f : BitVec 16) (c0 c1 c2 c3 : BitVec 1) :
    fswES (fswSetC f c0 c1 c2 c3) = fswES f := by
  unfold fswSetC
  rw [fswES_setSlice _ 14 1 _ (by omega), fswES_setSlice _ 10 1 _ (by omega),
    fswES_setSlice _ 9 1 _ (by omega), fswES_setSlice _ 8 1 _ (by omega)]

@[simp] theorem add_zero3 (x : BitVec 3) : x + 0#3 = x := BitVec.add_zero x

theorem add_zero3' (x : BitVec 3) : x + (0 : BitVec 3) = x := BitVec.add_zero x

theorem getElem_setSlice {n : Nat} (x : BitVec n) (lo w : Nat) (v : BitVec w) (k : Nat)
    (hk : k < n) :
    (setSlice x lo w v)[k] = if lo ≤ k ∧ k < lo + w then v.getLsbD (k - lo) else x[k] := by
  rw [← BitVec.getLsbD_eq_getElem, getLsbD_setSlice _ _ _ _ _ hk]
  split <;> simp [BitVec.getLsbD_eq_getElem hk]

set_option hygiene false in
/-- Bit-by-bit proof of an equation of status words (16 cases). -/
macro "fsw_bits" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases lt16_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    simp [fswRest, fswSetTop, fswOrFlags, fswSetC, getElem_setSlice]))

set_option hygiene false in
/-- Bit-by-bit proof of an equation of condition codes (4 cases). -/
macro "cc_bits" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [fswCC, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  rcases lt4_cases hi with rfl | rfl | rfl | rfl <;>
    simp [fswSetTop, fswOrFlags, fswSetC, getElem_setSlice]))

@[simp] theorem fswOrFlags_zero (f : BitVec 16) : fswOrFlags f 0#6 = f := by
  fsw_bits

@[simp] theorem fswSetTop_fswSetTop (f : BitVec 16) (a b : BitVec 3) :
    fswSetTop (fswSetTop f a) b = fswSetTop f b := by
  fsw_bits

/-- ORing exception flags into the status word commutes with setting TOP. -/
theorem fswOrFlags_fswSetTop (f : BitVec 16) (t : BitVec 3) (x : BitVec 6) :
    fswOrFlags (fswSetTop f t) x = fswSetTop (fswOrFlags f x) t := by
  fsw_bits

/-- Setting TOP to its value leaves the status word alone. -/
theorem fswSetTop_fswTop (f : BitVec 16) : fswSetTop f (fswTop f) = f := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [fswSetTop, fswTop]
  rw [getLsbD_setSlice _ _ _ _ _ hi]
  split
  · simp only [BitVec.getLsbD_extractLsb']
    rw [decide_eq_true (by omega), Bool.true_and]
    exact congrArg _ (by omega)
  · rfl

theorem fswRest_fswSetTop (f : BitVec 16) (t : BitVec 3) :
    fswRest (fswSetTop f t) = fswSetTop (fswRest f) t := by
  fsw_bits

@[simp] theorem fswRest_fswSetC (f : BitVec 16) (c0 c1 c2 c3 : BitVec 1) :
    fswRest (fswSetC f c0 c1 c2 c3) = fswRest f := by
  fsw_bits

@[simp] theorem fswCC_fswSetTop (f : BitVec 16) (t : BitVec 3) :
    fswCC (fswSetTop f t) = fswCC f := by
  cc_bits

@[simp] theorem fswCC_fswOrFlags (f : BitVec 16) (x : BitVec 6) :
    fswCC (fswOrFlags f x) = fswCC f := by
  cc_bits

@[simp] theorem fswCC_fswSetC (f : BitVec 16) (c0 c1 c2 c3 : BitVec 1) :
    fswCC (fswSetC f c0 c1 c2 c3) = c3 ++ c2 ++ c1 ++ c0 := by
  cc_bits

theorem fswRest_ite_setTop (c : Prop) [Decidable c] (x y : BitVec 16) (top : BitVec 3)
    (hx : fswRest x = y) :
    fswRest (if c then x else fswSetTop x top) = if c then y else fswSetTop y top := by
  split
  · exact hx
  · rw [fswRest_fswSetTop, hx]

theorem fswCC_ite_setTop (c : Prop) [Decidable c] (x : BitVec 16) (top : BitVec 3) :
    fswCC (if c then x else fswSetTop x top) = fswCC x := by
  split
  · rfl
  · exact fswCC_fswSetTop _ _

theorem unsigned_range {w : Nat} (x : BitVec w) (hw : w = 3) : 0 ≤ Unsigned x ∧ Unsigned x < 8 := by
  have : x.toNat < 8 := by subst hw; exact x.isLt
  simp only [unsigned_eq]
  omega

/-- The status word most x87 instructions leave: C1 := 0, C0, C2, C3 the oracle's next three
bits (lean-x86 sets them in that order: C0, C1, C2, C3). -/
def fswC1Zero (fsw : BitVec 16) (o : X86.Runtime.Oracle) : BitVec 16 :=
  fswSetC fsw (oBit o 0) 0 (oBit o 1) (oBit o 2)

@[simp] theorem fswTop_fswC1Zero (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fswTop (fswC1Zero fsw o) = fswTop fsw := fswTop_fswSetC _ _ _ _ _

@[simp] theorem fswES_fswC1Zero (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fswES (fswC1Zero fsw o) = fswES fsw := fswES_fswSetC _ _ _ _ _

@[simp] theorem fswRest_fswC1Zero (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fswRest (fswC1Zero fsw o) = fswRest fsw := fswRest_fswSetC _ _ _ _ _

theorem fswCC_fswC1Zero (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fswCC (fswC1Zero fsw o) &&& 2 = 0 := by
  simp only [fswC1Zero, fswCC_fswSetC]
  generalize oBit o 0 = a
  generalize oBit o 1 = b
  generalize oBit o 2 = c
  revert a b c
  decide

/-- The status word an x87 form leaves after a sign operation (FCHS, FABS) that reported
`fswC1Zero fsw o`: SF and the flags of that report, then C0, C1, C2, C3 set again (C0, C2, C3 the
oracle's next bits), exactly as lean-x86 computes it. -/
def x87UnaryStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) : BitVec 16 :=
  setSlice (setSlice (setSlice (setSlice
    (fswOrFlags (setSlice fsw 6 1 (FP87_Status_Type.SF (fswC1Zero fsw o)))
      (FP87_Status_Type.Exception_Flags (fswC1Zero fsw o)))
    8 1 (oBit o 3)) 9 1 (FP87_Status_Type.C1 (fswC1Zero fsw o))) 10 1 (oBit (oracleSkip o 3) 1))
    14 1 (oBit (oracleSkip (oracleSkip o 3) 1) 1)

theorem x87UnaryStatus_eq (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    x87UnaryStatus fsw o = fswC1Zero fsw (oracleSkip o 3) := by
  simp only [x87UnaryStatus, fswC1Zero, oBit, oracleSkip_oracleSkip]
  fsw_bits
  all_goals simp [FP87_Status_Type.SF, FP87_Status_Type.Exception_Flags, FP87_Status_Type.C1,
    getElem_setSlice]

/-- A status word with C1 := `c1`. -/
def fswSetC1 (fsw : BitVec 16) (c1 : BitVec 1) : BitVec 16 := setSlice fsw 9 1 c1

/-- The status an x87 store operation reports (`Operations.FST`, `FST_Convert`, `FIST`, as a
value: they leave the state alone): `fsw` with C1 := `c1` and the exception
flags `ex` ORed in. -/
def x87ReportFsw (fsw : BitVec 16) (c1 : BitVec 1) (ex : BitVec 6) : BitVec 16 :=
  fswOrFlags (fswSetC1 fsw c1) ex

/-- The status word an x87 form leaves when it commits the status `st` its operation reported, on
the current status word `cur` (after a pop, if any): SF and the exception flags of `st` (ORed in;
every exception is masked), C1 of `st`, and C0, C2, C3 the oracle's next three bits, exactly as
lean-x86 sets them (`setSF`, `Process_Exceptions`, then `setC0`, `setC1`, `setC2`, `setC3`). The
store forms (FST, FIST) commit this way after their memory write. -/
def x87CommitFsw (cur st : BitVec 16) (o : X86.Runtime.Oracle) : BitVec 16 :=
  setSlice (setSlice (setSlice (setSlice
    (fswOrFlags (setSlice cur 6 1 (st.extractLsb' 6 1)) (st.extractLsb' 0 6))
    8 1 (BitVec.ofBool (oracleBit o))) 9 1 (st.extractLsb' 9 1)) 10 1
    (BitVec.ofBool (oracleBit (oracleSkip o 1)))) 14 1
    (BitVec.ofBool (oracleBit (oracleSkip (oracleSkip o 1) 1)))

theorem x87CommitFsw_eq (cur st : BitVec 16) (o : X86.Runtime.Oracle) :
    x87CommitFsw cur st o =
      fswSetC (fswOrFlags (setSlice cur 6 1 (st.extractLsb' 6 1)) (st.extractLsb' 0 6))
        (oBit o 0) (st.extractLsb' 9 1) (oBit o 1) (oBit o 2) := by
  simp only [x87CommitFsw, oBit, oracleSkip_oracleSkip, oracleSkip_zero]
  rfl

@[simp] theorem fswTop_x87CommitFsw (cur st : BitVec 16) (o : X86.Runtime.Oracle) :
    fswTop (x87CommitFsw cur st o) = fswTop cur := by
  rw [x87CommitFsw_eq]
  simp (disch := omega) only [fswTop_fswSetC, fswTop_fswOrFlags, fswTop_setSlice]

@[simp] theorem fswES_x87CommitFsw (cur st : BitVec 16) (o : X86.Runtime.Oracle) :
    fswES (x87CommitFsw cur st o) = fswES cur := by
  rw [x87CommitFsw_eq]
  simp (disch := omega) only [fswES_fswSetC, fswES_fswOrFlags, fswES_setSlice]

/-- Committing commutes with setting TOP (a pop before the commit). -/
theorem x87CommitFsw_fswSetTop (cur st : BitVec 16) (top : BitVec 3) (o : X86.Runtime.Oracle) :
    x87CommitFsw (fswSetTop cur top) st o = fswSetTop (x87CommitFsw cur st o) top := by
  simp only [x87CommitFsw_eq]
  fsw_bits

/-- Committing a report that only clears C1 (FSTPNCE) is `fswC1Zero`. -/
theorem x87CommitFsw_c1Zero (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    x87CommitFsw fsw (fswSetC1 fsw 0) o = fswC1Zero fsw o := by
  simp only [x87CommitFsw_eq, fswC1Zero, fswSetC1]
  fsw_bits
  all_goals simp [getElem_setSlice]

/-- lean-x86's pure status update of the operations that report their status as a value,
`setException_Flags st (Exception_Flags st ||| ex)`, is `fswOrFlags`. -/
theorem setExceptionFlags_or (st : BitVec 16) (ex : BitVec 6)
    (h : (6 : Int).toNat = (6 : Int).toNat) :
    FP87_Status_Type.setException_Flags st
      ((BitVec.cast h (FP87_Status_Type.Exception_Flags st)).or ex) = fswOrFlags st ex := rfl

/-- A status word is its part outside the condition codes and its condition codes. -/
theorem fswRest_or_ccWord (f : BitVec 16) : fswRest f ||| ccWord (fswCC f) = f := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [fswRest, ccWord, fswCC, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_append]
  rcases lt16_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    simp

/-- `get` returns the state and leaves it as it is (stated with the state itself, not an
eta-expanded
copy, which keeps later kernel checks small). -/
theorem specM_get_run {ε σ : Type} (s : X86.State σ) :
    (get : SpecM ε (X86.State σ) (X86.State σ)).run s = (.ok s, s) := rfl

section Run

variable {σ : Type}

theorem fp87StatusTOP_run (s : X86.State σ) :
    (X86.FP87_Status.TOP : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (fswTop s.FP87_Status), s) := by
  simp [X86.FP87_Status.TOP, x86_runtime, fswTop]
  rfl

theorem toNat3_lt (i : BitVec 3) : (i.toNat : Int) < 8 := by have := i.isLt; omega

theorem toNat_lt8 {w : Nat} (j : BitVec w) (hw : w = 3) : j.toNat < 8 := by
  subst hw; exact j.isLt

section Monad

variable {m : Type → Type} [Monad m] {ε : Type} [MonadExcept (Error ε) m] [LawfulMonad m]

/-- A tag read out of the tag word at register index `n % 8`. -/
theorem sliceElement_tag (ftw : Bits 16) (n : Nat) :
    (sliceElement ftw 2 (((n % 8 : Nat) : Int)) : m (Bits 2)) =
      pure (ftw.extractLsb' ((n % 8) * 2) 2) := by
  have : n % 8 < 8 := Nat.mod_lt _ (by decide)
  rw [sliceElement_bitVec_eq_pure _ (by omega) (by omega) (by omega)]
  have e : (((n % 8 : Nat) : Int) * 2).toNat = (n % 8) * 2 := by omega
  simp only [e]
  rfl

/-- A tag set in the tag word at register index `n % 8`. -/
theorem setSliceChecked_tag (ftw : Bits 16) (n : Nat) (tag : Bits 2) :
    (setSliceChecked ftw (((n % 8 : Nat) : Int) * 2) 2 tag : m (Bits 16)) =
      pure (setSlice ftw ((n % 8) * 2) 2 tag) := by
  have : n % 8 < 8 := Nat.mod_lt _ (by decide)
  rw [setSliceChecked_eq_pure _ _ (by omega) (by omega) (by omega)]
  have e : (((n % 8 : Nat) : Int) * 2).toNat = (n % 8) * 2 := by omega
  simp only [e]
  rfl

omit [LawfulMonad m] in
theorem assert_toNatW_mul2 {w : Nat} (x : BitVec w) (hw : w = 3) :
    (assert (decide ((x.toNat : Int) * 2 ≤ 14)) : m Unit) = pure () := by
  have : x.toNat < 8 := by subst hw; exact x.isLt
  exact assert_of_true (by simp; omega)

omit [LawfulMonad m] in
theorem assert_toNatW_lt8 {w : Nat} (x : BitVec w) (hw : w = 3) :
    (assert (decide ((x.toNat : Int) < 8)) : m Unit) = pure () := by
  have : x.toNat < 8 := by subst hw; exact x.isLt
  exact assert_of_true (by simp; omega)

omit [LawfulMonad m] in
theorem assert_natCast_nonneg (n : Nat) : (assert (decide (0 ≤ (n : Int))) : m Unit) = pure () :=
  assert_of_true (by simp)

/-- A tag set in the tag word at the index of a 3-bit register number. -/
theorem setSliceChecked_tagW (ftw : Bits 16) {w : Nat} (x : BitVec w) (hw : w = 3)
    (tag : Bits 2) :
    (setSliceChecked ftw ((x.toNat : Int) * 2) 2 tag : m (Bits 16)) =
      pure (setSlice ftw (x.toNat * 2) 2 tag) := by
  have : x.toNat < 8 := by subst hw; exact x.isLt
  rw [setSliceChecked_eq_pure _ _ (by omega) (by omega) (by omega)]
  have e : ((x.toNat : Int) * 2).toNat = x.toNat * 2 := by omega
  simp only [e]
  rfl

/-- The ModRM `rm` field sliced out of itself (`rm[2:0]`), as the x87 forms take ST(i)'s
index. -/
theorem sliceInclusive_rm (rm : BitVec 3) :
    (sliceInclusive rm 2 0 : m (Bits (2 - 0 + 1))) = pure rm := by
  rw [sliceInclusive_eq_pure _ (by decide) (by decide) (by decide)]
  simp

end Monad

theorem decide_toNatW_mul2 {w : Nat} (x : BitVec w) (hw : w = 3) :
    decide ((x.toNat : Int) * 2 ≤ 14) = true := by
  have := toNat_lt8 x hw
  simp; omega

theorem decide_toNatW_lt8 {w : Nat} (x : BitVec w) (hw : w = 3) :
    decide ((x.toNat : Int) < 8) = true := by
  have := toNat_lt8 x hw
  simp; omega

theorem decide_mod8_mul2 (n : Nat) : decide (((n % 8 : Nat) : Int) * 2 ≤ 14) = true := by
  have : n % 8 < 8 := Nat.mod_lt _ (by decide)
  simp; omega

theorem decide_mod8_lt8 (n : Nat) : decide (((n % 8 : Nat) : Int) < 8) = true := by
  have : n % 8 < 8 := Nat.mod_lt _ (by decide)
  simp; omega

theorem decide_natCast_nonneg (n : Nat) : decide (0 ≤ (n : Int)) = true := by simp

theorem addInt_mod8 (a b : Nat) : ((a : Int) + (b : Int)) % 8 = (((b + a) % 8 : Nat) : Int) := by
  omega

/-- `TOP + i` as lean-x86 computes a register-stack index (`Std.Bits.Add_int` at 3 bits). -/
theorem toNat_add_ofInt {w : Nat} (x : BitVec w) (i : BitVec 3) (hw : w = 3) :
    (x + BitVec.ofInt w (i.toNat : Int)).toNat = (x.toNat + i.toNat) % 8 := by
  subst hw
  rw [BitVec.toNat_add]
  simp

theorem toNat_add3 (x i : BitVec 3) : (x + i).toNat = (x.toNat + i.toNat) % 8 := by
  rw [BitVec.toNat_add]

theorem st_run (s : X86.State σ) (k : Int) (i : BitVec 3) (hk : k = (i.toNat : Int))
    (hne : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + i) ≠ 3) :
    (X86.Helpers.ST k : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok s.FP87[fprIndex (fswTop s.FP87_Status + i)], s) := by
  subst hk
  unfold X86.Helpers.ST
  simp only [assert_of_true (by simp [toNat3_lt] : decide ((i.toNat : Int) < 8) = true),
    pure_bind]
  refine (specM_bind_run _ _ (fp87StatusTOP_run _)).trans ?_
  simp only [stdAddInt_eq_ok _ _ (by decide : (0 : Int) ≤ 3), liftM_ok, pure_bind, unsigned_eq,
    toNat_add_ofInt _ _ (rfl : Int.toNat 3 = 3), assert_of_true (decide_mod8_mul2 _),
    assert_of_true (decide_mod8_lt8 _), assert_of_true (decide_natCast_nonneg _),
    sliceElement_tag]
  simp only [← toNat_add3]
  refine (specM_bind_run _ _ rfl).trans ?_
  have hne' : (BitVec.extractLsb' ((fswTop s.FP87_Status + i).toNat * 2) 2 s.FP87_Tag_Word == 3) =
      false := by simpa [ftwTag] using hne
  simp only [hne', Bool.false_eq_true, ↓reduceIte]
  exact fp87Get_run _ _ _ rfl

/-- `FP87.Read_STi k` reads ST(`i`) whatever its tag, and changes nothing (unlike `ST`, which sets
SF for an empty register): the forms that use it report the stack fault in their operation. -/
theorem readSTi_run (s : X86.State σ) (k : Int) (i : BitVec 3) (hk : k = (i.toNat : Int)) :
    (FP87.Read_STi k : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok s.FP87[fprIndex (fswTop s.FP87_Status + i)], s) := by
  subst hk
  unfold FP87.Read_STi FP87.Get_Stack_Index
  simp only [assert_of_true (by simp [toNat3_lt] : decide ((i.toNat : Int) < 8) = true),
    pure_bind, bind_assoc]
  refine (specM_bind_run _ _ (fp87StatusTOP_run _)).trans ?_
  simp only [unsigned_eq, stdPositiveRemainder_eq_pure
    (Int.add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)) (by decide : (0 : Int) < 8),
    addInt_mod8, assert_of_true (decide_mod8_lt8 _), assert_of_true (decide_natCast_nonneg _),
    pure_bind]
  simp only [← toNat_add3]
  exact fp87Get_run _ _ _ rfl

theorem fp87StatusFlags_run (s : X86.State σ) :
    (X86.FP87_Status.Exception_Flags : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (s.FP87_Status.extractLsb' 0 6), s) := by
  simp [X86.FP87_Status.Exception_Flags, x86_runtime]
  rfl

theorem fp87ControlMasks_run (s : X86.State σ) :
    (X86.FP87_Control.Exception_Masks : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (s.FP87_Control.extractLsb' 0 6), s) := by
  simp [X86.FP87_Control.Exception_Masks, x86_runtime]
  rfl

theorem fp87ControlIM_run (s : X86.State σ) :
    (X86.FP87_Control.IM : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (s.FP87_Control.extractLsb' 0 1), s) := by
  simp [X86.FP87_Control.IM, x86_runtime]
  rfl

/-- A one-bit `UNSPECIFIED` is the oracle's next bit; it uses that bit up. -/
theorem unspecified1_run (s : X86.State σ) :
    (UNSPECIFIED (size := 1) : SpecM X86.Exception (X86.State σ) (Bits 1)).run s =
      (.ok (BitVec.ofBool (oracleBit s.oracle)), { s with oracle := oracleSkip s.oracle 1 }) := by
  have h := oracleTake_one s.oracle
  simp [UNSPECIFIED, x86_runtime, get, getThe, MonadStateOf.get, set, MonadStateOf.set, bind, pure,
    ExceptT.bind, ExceptT.run, ExceptT.mk, StateT.bind, ExceptT.bindCont, liftM, monadLift,
    MonadLift.monadLift, ExceptT.pure, StateT.pure, StateT.get, StateT.set, ExceptT.lift,
    Functor.map, StateT.map, h]

theorem isSTiEmpty_run' (s : X86.State σ) (k : Int) (i : BitVec 3) (hk : k = (i.toNat : Int)) :
    (FP87.Is_STi_Empty k : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + i) == 3), s) := by
  subst hk
  unfold FP87.Is_STi_Empty FP87.Get_Stack_Index
  simp only [bind_assoc]
  refine (specM_bind_run _ _ (fp87StatusTOP_run _)).trans ?_
  simp only [unsigned_eq, stdPositiveRemainder_eq_pure
    (Int.add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)) (by decide : (0 : Int) < 8),
    addInt_mod8, assert_of_true (decide_mod8_mul2 _), assert_of_true (decide_natCast_nonneg _),
    pure_bind, sliceElement_tag]
  simp only [← toNat_add3]
  rfl

theorem stWrite_run (s : X86.State σ) (k : Int) (i : BitVec 3) (hk : k = (i.toNat : Int))
    (v : BitVec 80) :
    (ST_write k v : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (), { s with
        FP87_Tag_Word := ftwSet s.FP87_Tag_Word (fswTop s.FP87_Status + i) (x87Tag v)
        FP87 := fprSet s.FP87 (fswTop s.FP87_Status + i) v }) := by
  subst hk
  unfold ST_write X86.FP87_Tag_Word.setSlice
  simp only [assert_of_true (by simp [toNat3_lt] : decide ((i.toNat : Int) < 8) = true),
    pure_bind]
  refine (specM_bind_run _ _ (fp87StatusTOP_run _)).trans ?_
  simp only [stdAddInt_eq_ok _ _ (by decide : (0 : Int) ≤ 3), liftM_ok, pure_bind, unsigned_eq,
    toNat_add_ofInt _ _ (rfl : Int.toNat 3 = 3), assert_of_true (decide_mod8_mul2 _),
    assert_of_true (decide_mod8_lt8 _), assert_of_true (decide_natCast_nonneg _),
    setSliceChecked_tag, getTagWordValue_eq]
  simp only [← toNat_add3]
  spec_run [X86.FP87.set => fp87Set_run _ _ _ rfl _]

/-- `ST_write k v` for `0 ≤ k < 8`, the index as a 3-bit value. -/
theorem stWrite_run' (s : X86.State σ) (k : Int) (hk : 0 ≤ k ∧ k < 8) (v : BitVec 80) :
    (ST_write k v : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (), { s with
        FP87_Tag_Word := ftwSet s.FP87_Tag_Word (fswTop s.FP87_Status + BitVec.ofInt 3 k) (x87Tag v)
        FP87 := fprSet s.FP87 (fswTop s.FP87_Status + BitVec.ofInt 3 k) v }) := by
  have e : k = ((BitVec.ofInt 3 k).toNat : Int) := by
    simp only [BitVec.toNat_ofInt]
    omega
  exact stWrite_run s k _ e v

theorem subInt3_one (x : Bits 3) :
    X86.Helpers.Std.Bits.Subtract_int (n := 3) x 1 = .ok (x - 1) := by
  rw [stdSubtractInt_eq_ok _ _ (by decide)]
  rfl

theorem addInt3_one (x : Bits 3) :
    X86.Helpers.Std.Bits.Add_int (n := 3) x 1 = .ok (x + 1) := by
  rw [stdAddInt_eq_ok _ _ (by decide)]
  rfl

theorem fp87StatusSetTOP_run' (s : X86.State σ) (v : Bits 3) :
    (X86.FP87_Status.setTOP v : SpecM X86.Exception (X86.State σ) Unit).run s =
      (.ok (), { s with FP87_Status := fswSetTop s.FP87_Status v }) := rfl

/-- `FP87.Push`: TOP := TOP − 1. -/
theorem push_run (s : X86.State σ) :
    (FP87.Push : SpecM X86.Exception (X86.State σ) Unit).run s =
      (.ok (), { s with FP87_Status := fswSetTop s.FP87_Status (fswTop s.FP87_Status - 1) }) := by
  unfold FP87.Push
  spec_run [X86.FP87_Status.TOP => fp87StatusTOP_run _,
    liftM => liftM_run_of_ok (subInt3_one _) _]

/-- `FP87.Pop`: the tag of ST(0) := empty (3), then TOP := TOP + 1. -/
theorem pop_run (s : X86.State σ) :
    (FP87.Pop : SpecM X86.Exception (X86.State σ) Unit).run s =
      (.ok (), { s with
        FP87_Tag_Word := ftwSet s.FP87_Tag_Word (fswTop s.FP87_Status) 3
        FP87_Status := fswSetTop s.FP87_Status (fswTop s.FP87_Status + 1) }) := by
  unfold FP87.Pop X86.FP87_Tag_Word.setSlice
  simp only [unsigned_eq, assert_toNatW_mul2, assert_natCast_nonneg, pure_bind,
    setSliceChecked_tagW, Int.reduceToNat]
  spec_run [X86.FP87_Status.TOP => fp87StatusTOP_run _,
    liftM => liftM_run_of_ok (addInt3_one _) _]

theorem isUnmaskedException_masked (f : BitVec 6) :
    FP87.Is_Unmasked_Exception f 63 = .ok false := by
  unfold FP87.Is_Unmasked_Exception
  rw [show (f &&& ~~~(63 : BitVec 6)) = f &&& ~~~(63 : BitVec 6) from rfl]
  simp only [bind, Except.bind, isZero_masked]
  rfl

/-- With every exception masked, `FP87.Process_Exceptions f` ORs the flags `f` into the status
word and sets neither ES nor B. -/
theorem processExceptions_run (s : X86.State σ) (f : BitVec 6)
    (hm : FcwMasked s.FP87_Control) :
    (FP87.Process_Exceptions f : SpecM X86.Exception (X86.State σ) Unit).run s =
      (.ok (), { s with FP87_Status := fswOrFlags s.FP87_Status f }) := by
  unfold FP87.Process_Exceptions
  unfold FcwMasked at hm
  spec_run [X86.FP87_Status.Exception_Flags => fp87StatusFlags_run _,
    X86.FP87_Control.Exception_Masks => fp87ControlMasks_run _]
  simp only [hm, prioritizeExceptions_masked]
  spec_run [X86.FP87_Control.Exception_Masks => fp87ControlMasks_run _,
    liftM => liftM_run_of_ok (by rw [hm]; exact isUnmaskedException_masked f) _]

/-- `FP87.Free k` tags ST(`i`) empty. -/
theorem free_run (s : X86.State σ) (k : Int) (i : BitVec 3) (hk : k = (i.toNat : Int)) :
    (FP87.Free k : SpecM X86.Exception (X86.State σ) Unit).run s =
      (.ok (), { s with
        FP87_Tag_Word := ftwSet s.FP87_Tag_Word (fswTop s.FP87_Status + i) 3 }) := by
  subst hk
  unfold FP87.Free X86.FP87_Tag_Word.setSlice
  have h07 : inRange (i.toNat : Int) 0 7 = true := by
    have := i.isLt
    simp only [inRange_eq, decide_eq_true_eq, Bool.and_eq_true]
    omega
  simp only [assert_of_true h07, pure_bind]
  refine (specM_bind_run _ _ (fp87StatusTOP_run _)).trans ?_
  simp only [stdAddInt_eq_ok _ _ (by decide : (0 : Int) ≤ 3), liftM_ok, pure_bind, unsigned_eq,
    toNat_add_ofInt _ _ (rfl : Int.toNat 3 = 3), assert_of_true (decide_mod8_mul2 _),
    assert_of_true (decide_natCast_nonneg _), setSliceChecked_tag]
  simp only [← toNat_add3]
  rfl

/-- `FP87.Is_STi_Empty k` for `0 ≤ k < 8`: whether ST(`k`) is tagged empty. -/
theorem isSTiEmpty_run (s : X86.State σ) (k : Int) (hk : 0 ≤ k ∧ k < 8) :
    (FP87.Is_STi_Empty k : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + BitVec.ofInt 3 k) == 3), s) := by
  have e : k = ((BitVec.ofInt 3 k).toNat : Int) := by
    simp only [BitVec.toNat_ofInt]
    omega
  exact isSTiEmpty_run' s k _ e

@[simp] theorem ofInt3_unsigned (i : BitVec 3) : BitVec.ofInt 3 (Unsigned i) = i := by
  simp [unsigned_eq]

theorem isUnmaskedPre_masked {σ : Type} (s : X86.State σ) (f : BitVec 6)
    (hm : FcwMasked s.FP87_Control) :
    (FP87.Is_Unmasked_Pre_Computation_Exception f : SpecM X86.Exception (X86.State σ) Bool).run s =
      (.ok false, s) := by
  unfold FP87.Is_Unmasked_Pre_Computation_Exception
  unfold FcwMasked at hm
  spec_run [X86.FP87_Control.Exception_Masks => fp87ControlMasks_run _]
  simp only [hm]
  simp [x86_runtime]

theorem fp87ControlRC_run (s : X86.State σ) :
    (X86.FP87_Control.RC : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (s.FP87_Control.extractLsb' 10 2), s) := by
  simp [X86.FP87_Control.RC, x86_runtime]
  rfl

end Run

/-- The normalization the x87 operation proofs use on branch conditions: register-stack
indices, TOP after condition-code writes, and Boolean connectives. -/
macro "x87_cond" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := omega) only [$ls,*, ofInt3_unsigned, fswTop_setSlice, fswES_setSlice,
    show BitVec.ofInt 3 0 = 0 from rfl, show BitVec.ofInt 3 7 = 7 from rfl, add_zero3,
    add_zero3',
    Bool.not_false, Bool.true_and, Bool.not_true, Bool.or_false, Bool.false_eq_true,
    ↓reduceIte, HAnd.hAnd, AndOp.and, HOr.hOr, OrOp.or, Bool.and_false, Bool.and_true,
    Bool.false_or, Bool.or_true, Bool.false_and, Bool.not_not, strictAnd, strictOr]))

end X86Proofs
