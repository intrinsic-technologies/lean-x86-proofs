import X86Proofs.Core.Shift
import X86Proofs.Program.ReadWrite.WritePair

/-!
# MUL specification

One-operand unsigned multiply: `RDX:RAX ← RAX ∗ SRC` (`EDX:EAX ← EAX ∗ SRC`, `DX:AX ← AX ∗ SRC`;
`AX ← AL ∗ SRC` at 8 bits). The product of two `n`-bit values has `2n` bits; `mulResult` gives its
low half (RAX, or AL), the product truncated (`mulResult_fst`), and high half (RDX, or AH).

Flags (Intel SDM): CF and OF are cleared if the high half of the product is zero, and set
otherwise; SF, ZF, AF and PF are undefined. lean-x86 draws the four undefined flags from its oracle
in the order SF, ZF, AF, PF; the spec takes them as `u 0`, `u 1`, `u 2`, `u 3`. `mulFlags` is the
same as a `StatusFlagsOutcome`, the undefined flags `none`.
-/

namespace X86Proofs

/-- The unsigned `2n`-bit product of `x` and `y`, as (low half, high half). -/
def mulResult {n : Nat} (x y : BitVec n) : BitVec n × BitVec n :=
  let p := BitVec.ofNat (n + n) (x.toNat * y.toNat)
  (p.extractLsb' 0 n, p.extractLsb' n n)

/-- Result and flags of MUL: the low and high halves of `x ∗ y` and the flags, with `u` the
unspecified bits for SF, ZF, AF, PF (in that order). -/
def mulSpec {n : Nat} (u : Nat → Bool) (x y : BitVec n) : BitVec n × BitVec n × StatusFlags :=
  let r := mulResult x y
  let c := r.2 != 0
  (r.1, r.2, { CF := c, OF := c, SF := u 0, ZF := u 1, AF := u 2, PF := u 3 })

/-- What MUL does to the flags: CF and OF say the high half of the product is not zero; SF, ZF,
AF and PF are undefined. -/
def mulFlags {n : Nat} (x y : BitVec n) : StatusFlagsOutcome :=
  let c := (mulResult x y).2 != 0
  { CF := some c, OF := some c, SF := none, ZF := none, AF := none, PF := none }

theorem mulFlags_allows {n : Nat} (u : Nat → Bool) (x y : BitVec n) :
    (mulFlags x y).Allows (mulSpec u x y).2.2 :=
  ⟨rfl, trivial, trivial, trivial, trivial, rfl⟩

/-- The low half of the double-width product is the product. -/
theorem mulResult_fst {n : Nat} (a b : BitVec n) : (mulResult a b).1 = a * b := by
  apply BitVec.eq_of_toNat_eq
  simp [mulResult, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (Nat.le_add_right n n))]

open X86 X86.Helpers

theorem ofInt_natMul_lo (n a b : Nat) :
    BitVec.ofInt n ((a : Int) * (b : Int) / 2 ^ 0) =
      (BitVec.ofNat (n + n) (a * b)).extractLsb' 0 n := by
  apply BitVec.eq_of_toNat_eq
  rw [Int.pow_zero, Int.ediv_one, ← Int.natCast_mul, BitVec.ofInt_natCast]
  simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

theorem ofInt_natMul_hi (n a b : Nat) :
    BitVec.ofInt n ((a : Int) * (b : Int) / 2 ^ n) =
      (BitVec.ofNat (n + n) (a * b)).extractLsb' n n := by
  apply BitVec.eq_of_toNat_eq
  rw [← Int.natCast_mul, show ((2 : Int) ^ n) = ((2 ^ n : Nat) : Int) by simp, ← Int.natCast_ediv,
    BitVec.ofInt_natCast]
  simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.pow_add, Nat.mod_mul_right_div_self, Nat.mod_mod]

theorem extractLsb'_append_extractLsb' {n : Nat} (p : BitVec (n + n)) :
    p.extractLsb' n n ++ p.extractLsb' 0 n = p := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_append]
  by_cases h : k < n
  · simp [h]
  · simp only [h, ↓reduceIte, BitVec.getLsbD_extractLsb', show k - n < n by omega,
      decide_true, Bool.true_and, show n + (k - n) = k by omega]

theorem ofInt_natMul (n a b : Nat) :
    BitVec.ofInt n ((a : Int) * (b : Int) / 2 ^ 0) = BitVec.ofNat n (a * b) := by
  rw [Int.pow_zero, Int.ediv_one, ← Int.natCast_mul, BitVec.ofInt_natCast]

theorem mul_operation {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ) (n : Nat)
    (hn : n = 16 ∨ n = 32 ∨ n = 64) (x : BitVec n) :
    (X86.Instructions.Operations.MUL n x).run s =
      let r := mulSpec (fun i => oracleBit (oracleSkip s.oracle i))
        ((Operand.reg 0 : Operand n).read s) x
      (.ok (), (Operand.reg 2 : Operand n).write ((Operand.reg 0 : Operand n).write
        (setFlags { s with oracle := oracleSkip s.oracle 4 } r.2.2) r.1) r.2.1) := by
  rcases hn with rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.MUL
    simp only [x86_runtime, liftM_ok]
    spec_bind_rfl
    spec_bind_with raxLow_run s _ (by decide)
    simp only [Int.reduceToNat, ofInt_natMul_lo, ofInt_natMul_hi]
    spec_bind_rfl
    spec_bind_rfl
    spec_bind_with rax_run _
    spec_bind_with liftM_mergeGPR_run _ _ (by decide) _ _
    spec_bind_with raxWrite_run _ _
    spec_bind_with rdx_run _
    spec_bind_with liftM_mergeGPR_run _ _ (by decide) _ _
    spec_bind_with rdxWrite_run _ _
    rw [← Operand.write_reg_eq_set, ← Operand.write_reg_eq_set]
    simp only [Operand.write_write_setFlags]
    simp only [mulSpec, mulResult, Operand.read_reg64, Operand.read_reg32, Operand.read_reg16,
      BitVec.setWidth_eq, Int.reduceToNat]
    generalize hT : (Operand.reg 2 : Operand _).write ((Operand.reg 0 : Operand _).write s _) _ = T
    have hTo : s.oracle = T.oracle := by subst hT; rfl
    repeat spec_bind_rfl
    rw [rflagsSetCF_run]
    dsimp only
    simp only [hTo]
    rw [setFlags_eq_of_store]
    · rfl
    · rflags_ext

theorem mul_operation8 {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (x : BitVec 8) :
    (X86.Instructions.Operations.MUL 8 x).run s =
      let r := mulSpec (fun i => oracleBit (oracleSkip s.oracle i))
        ((Operand.reg 0 : Operand 8).read s) x
      (.ok (), (Operand.reg 0 : Operand 16).write
        (setFlags { s with oracle := oracleSkip s.oracle 4 } r.2.2) (r.2.1 ++ r.1)) := by
  unfold X86.Instructions.Operations.MUL
  simp only [x86_runtime, liftM_ok]
  spec_bind_rfl
  spec_bind_with raxLow_run s _ (by decide)
  simp only [Int.reduceToNat, sliceInclusive_eq, Int.reduceSub, Int.reduceAdd,
    x86_runtime, ofInt_natMul_hi]
  spec_bind_rfl
  rw [ofInt_natMul]
  spec_bind_with axWrite_run _ _
  rw [← Operand.write_reg_eq_set]
  simp only [Operand.write_setFlags]
  simp only [mulSpec, mulResult, extractLsb'_append_extractLsb']
  simp only [Operand.read_reg8, Int.reduceToNat, Nat.reduceAdd]
  generalize hT : (Operand.reg 0 : Operand 16).write s _ = T
  have hTo : s.oracle = T.oracle := by subst hT; rfl
  repeat spec_bind_rfl
  rw [rflagsSetCF_run]
  dsimp only
  simp only [hTo]
  rw [setFlags_eq_of_store]
  · rfl
  · rflags_ext

attribute [x86_compose] mulFlags

end X86Proofs
