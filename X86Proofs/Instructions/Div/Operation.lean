import X86Proofs.Core.Shift
import X86Proofs.Program.ReadWrite.WritePair

/-!
# DIV specification

One-operand unsigned divide: the `2n`-bit dividend `RDX:RAX` (`EDX:EAX`, `DX:AX`; `AX` at 8 bits)
divided by the `n`-bit source, the quotient to RAX (EAX, AX; AL) and the remainder to RDX (EDX,
DX; AH). `divResult t d` is (quotient, remainder).

The SDM raises #DE (divide error) when the divisor is zero or the quotient does not fit in `n`
bits. lean-x86 does the same: `Report_Divide_Error` throws the #DE exception, so the step does not
complete normally. `DivDefined t d` is the condition under which DIV completes (divisor nonzero,
quotient below `2 ^ n`); the operation lemma and every DIV effect assume it.

Flags: all six (CF, OF, SF, ZF, AF, PF) are undefined. lean-x86 draws them from its oracle in the
order OF, SF, ZF, AF, PF, CF; the spec takes them as `u 0`, …, `u 5`. `divFlags` leaves every flag
undefined.
-/

namespace X86Proofs

/-- Quotient and remainder of the unsigned division of the `2n`-bit dividend `t` by `d`. -/
def divResult {n : Nat} (t : BitVec (n + n)) (d : BitVec n) : BitVec n × BitVec n :=
  (BitVec.ofNat n (t.toNat / d.toNat), BitVec.ofNat n (t.toNat % d.toNat))

/-- DIV of `t` by `d` completes (no #DE): the divisor is not zero and the quotient fits in `n`
bits. -/
def DivDefined {n : Nat} (t : BitVec (n + n)) (d : BitVec n) : Prop :=
  d ≠ 0 ∧ t.toNat / d.toNat < 2 ^ n

/-- Result and flags of DIV: quotient, remainder and the flags, with `u` the unspecified bits for
OF, SF, ZF, AF, PF, CF (in that order). -/
def divSpec {n : Nat} (u : Nat → Bool) (t : BitVec (n + n)) (d : BitVec n) :
    BitVec n × BitVec n × StatusFlags :=
  let r := divResult t d
  (r.1, r.2, { OF := u 0, SF := u 1, ZF := u 2, AF := u 3, PF := u 4, CF := u 5 })

/-- What DIV does to the flags: every flag is undefined. -/
def divFlags : StatusFlagsOutcome :=
  { CF := none, OF := none, SF := none, ZF := none, AF := none, PF := none }

theorem divFlags_allows {n : Nat} (u : Nat → Bool) (t : BitVec (n + n)) (d : BitVec n) :
    divFlags.Allows (divSpec u t d).2.2 :=
  ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

open X86 X86.Helpers

theorem toNat_append_eq {n m : Nat} (x : BitVec n) (y : BitVec m) :
    (x ++ y).toNat = x.toNat * 2 ^ m + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

theorem toNat_ofNat_concat (k n : Nat) (x y : BitVec n) (hk : n + n ≤ k) :
    (BitVec.ofNat k (x.toNat <<< n + y.toNat)).toNat = x.toNat * 2 ^ n + y.toNat := by
  have hx := x.isLt
  have hy := y.isLt
  have hlt : x.toNat * 2 ^ n + y.toNat < 2 ^ k :=
    calc x.toNat * 2 ^ n + y.toNat < (x.toNat + 1) * 2 ^ n := by rw [Nat.succ_mul]; omega
      _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul_right _ hx
      _ = 2 ^ (n + n) := (Nat.pow_add 2 n n).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  rw [BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hlt]

theorem div_check (n T d : Nat) (hd : 0 < d) (h : T / d < 2 ^ n) :
    ¬ (((BitVec.ofInt n ((T : Int) / 2 ^ n)).toNat : Int) ≥ (d : Int)) := by
  rw [show ((T : Int) / 2 ^ n) = ((T / 2 ^ n : Nat) : Int) by simp, BitVec.ofInt_natCast,
    BitVec.toNat_ofNat]
  have h1 : T < 2 ^ n * d := (Nat.div_lt_iff_lt_mul hd).mp h
  have h2 : T / 2 ^ n < d := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n)).mpr (by
    rw [Nat.mul_comm]; exact h1)
  have h3 := Nat.mod_le (T / 2 ^ n) (2 ^ n)
  omega

theorem ofInt_tdiv_natCast (n T d : Nat) :
    BitVec.ofInt n (((T : Int).tdiv (d : Int)) / 2 ^ 0) = BitVec.ofNat n (T / d) := by
  rw [← Int.ofNat_tdiv, Int.pow_zero, Int.ediv_one, BitVec.ofInt_natCast]

theorem ofInt_tmod_natCast (n T d : Nat) :
    BitVec.ofInt n (((T : Int).tmod (d : Int)) / 2 ^ 0) = BitVec.ofNat n (T % d) := by
  rw [← Int.ofNat_tmod, Int.pow_zero, Int.ediv_one, BitVec.ofInt_natCast]

set_option hygiene false in
local macro "div_steps" rd:ident ra:ident wd:ident wa:ident fold:ident : tactic => `(tactic| (
  simp only [Operand.read_reg64, Operand.read_reg32, Operand.read_reg16] at hchk ⊢
  unfold X86.Instructions.Operations.DIV
  simp only [x86_runtime]
  spec_bind_rfl
  spec_bind_with $rd _
  spec_bind_with $ra _
  spec_bind_rfl
  spec_bind_rfl
  simp only [hx0, Bool.false_eq_true, ↓reduceIte, stdTruncatedDivide_eq_pure _ _ hxi,
    stdTruncatedRemainder_eq_pure _ _ hxi]
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_rfl
  simp (disch := decide) only [toNat_ofNat_concat]
  simp only [hchk, ↓reduceIte, sliceInclusive_eq, x86_runtime, ofInt_tdiv_natCast,
    ofInt_tmod_natCast]
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_with $wd _ _
  spec_bind_with $wa _ _
  rw [← $fold, ← $fold]
  simp only [Operand.write_write_setFlags]
  simp only [divSpec, divResult, toNat_append_eq, Int.reduceToNat]
  generalize hT : (Operand.reg 0 : Operand _).write ((Operand.reg 2 : Operand _).write s _) _ = T
  have hTo : s.oracle = T.oracle := by subst hT; rfl
  repeat spec_bind_rfl
  rw [rflagsSetCF_run]
  dsimp only
  simp only [hTo]
  rw [setFlags_eq_of_store]
  · rfl
  · rflags_ext))

theorem div_operation {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ) (n : Nat)
    (hn : n = 16 ∨ n = 32 ∨ n = 64) (x : BitVec n)
    (h : DivDefined ((Operand.reg 2 : Operand n).read s ++ (Operand.reg 0 : Operand n).read s) x) :
    (X86.Instructions.Operations.DIV n x).run s =
      let r := divSpec (fun i => oracleBit (oracleSkip s.oracle i))
        ((Operand.reg 2 : Operand n).read s ++ (Operand.reg 0 : Operand n).read s) x
      (.ok (), (Operand.reg 0 : Operand n).write ((Operand.reg 2 : Operand n).write
        (setFlags { s with oracle := oracleSkip s.oracle 6 } r.2.2) r.2.1) r.1) := by
  obtain ⟨hx, hq⟩ := h
  have hpos : 0 < x.toNat := by
    have : x.toNat ≠ 0 := fun e => hx (BitVec.eq_of_toNat_eq (by simpa using e))
    omega
  have hx0 : ((x.toNat : Int) == 0) = false := by simp; omega
  have hxi : (x.toNat : Int) ≠ 0 := by omega
  rw [toNat_append_eq] at hq
  have hchk := div_check _ _ _ hpos hq
  rcases hn with rfl | rfl | rfl
  · div_steps dx_run ax_run dxWrite_run axWrite_run Operand.write_reg_eq_set
  · div_steps edx_run eax_run edxWrite_run eaxWrite_run Operand.write_reg_eq_set
  · div_steps rdx_run rax_run rdxWrite_run raxWrite_run Operand.write_reg64

theorem div_operation8 {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (x : BitVec 8) (h : DivDefined ((Operand.reg 0 : Operand 16).read s) x) :
    (X86.Instructions.Operations.DIV 8 x).run s =
      let r := divSpec (fun i => oracleBit (oracleSkip s.oracle i))
        ((Operand.reg 0 : Operand 16).read s) x
      (.ok (), (Operand.reg 0 : Operand 16).write
        (setFlags { s with oracle := oracleSkip s.oracle 6 } r.2.2) (r.2.1 ++ r.1)) := by
  obtain ⟨hx, hq⟩ := h
  have hpos : 0 < x.toNat := by
    have : x.toNat ≠ 0 := fun e => hx (BitVec.eq_of_toNat_eq (by simpa using e))
    omega
  have hx0 : ((x.toNat : Int) == 0) = false := by simp; omega
  have hxi : (x.toNat : Int) ≠ 0 := by omega
  have hchk := div_check _ _ _ hpos hq
  simp only [Operand.read_reg16] at hchk ⊢
  unfold X86.Instructions.Operations.DIV
  simp only [x86_runtime]
  spec_bind_rfl
  spec_bind_with ax_run _
  spec_bind_rfl
  simp only [hx0, Bool.false_eq_true, ↓reduceIte, stdTruncatedDivide_eq_pure _ _ hxi,
    stdTruncatedRemainder_eq_pure _ _ hxi]
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_rfl
  simp only [hchk, ↓reduceIte, sliceInclusive_eq, x86_runtime, ofInt_tdiv_natCast,
    ofInt_tmod_natCast]
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_with ahWrite_run _ _
  spec_bind_with alWrite_run _ _
  rw [← Operand.write_reg_eq_set, Operand.write_reg8_setSlice_high]
  simp only [Operand.write_setFlags]
  simp only [divSpec, divResult]
  generalize hT : (Operand.reg 0 : Operand 16).write s _ = T
  have hTo : s.oracle = T.oracle := by subst hT; rfl
  repeat spec_bind_rfl
  rw [rflagsSetCF_run]
  dsimp only
  simp only [hTo]
  rw [setFlags_eq_of_store]
  · rfl
  · rflags_ext

attribute [x86_compose] divFlags

end X86Proofs
