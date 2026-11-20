import X86Proofs.Instructions.Div.Operation

/-!
# IDIV specification

One-operand signed divide: the `2n`-bit dividend `RDX:RAX` (`EDX:EAX`, `DX:AX`; `AX` at 8 bits)
divided by the `n`-bit source, as two's-complement integers, rounding toward zero; the quotient to
RAX (EAX, AX; AL) and the remainder (with the sign of the dividend) to RDX (EDX, DX; AH).
`idivResult t d` is (quotient, remainder).

The SDM raises #DE (divide error) when the divisor is zero or the quotient is outside the signed
`n`-bit range `-2 ^ (n - 1) … 2 ^ (n - 1) - 1` (e.g. the most negative dividend divided by -1).
lean-x86 does the same (`Report_Divide_Error` throws #DE, so the step does not complete normally).
`IdivDefined t d` is the condition under which IDIV completes; the operation lemma and every IDIV
effect assume it.

Flags: all six are undefined, drawn from lean-x86's oracle in the order OF, SF, ZF, AF, PF, CF
(`u 0`, …, `u 5`), as for DIV (`divFlags`).
-/

namespace X86Proofs

/-- Quotient (rounded toward zero) and remainder of the signed division of the `2n`-bit dividend
`t` by `d`. -/
def idivResult {n : Nat} (t : BitVec (n + n)) (d : BitVec n) : BitVec n × BitVec n :=
  (BitVec.ofInt n (t.toInt.tdiv d.toInt), BitVec.ofInt n (t.toInt.tmod d.toInt))

/-- IDIV of `t` by `d` completes (no #DE): the divisor is not zero and the quotient fits in `n`
signed bits. -/
def IdivDefined {n : Nat} (t : BitVec (n + n)) (d : BitVec n) : Prop :=
  d ≠ 0 ∧ -2 ^ (n - 1) ≤ t.toInt.tdiv d.toInt ∧ t.toInt.tdiv d.toInt < 2 ^ (n - 1)

/-- Result and flags of IDIV: quotient, remainder and the flags, with `u` the unspecified bits for
OF, SF, ZF, AF, PF, CF (in that order). -/
def idivSpec {n : Nat} (u : Nat → Bool) (t : BitVec (n + n)) (d : BitVec n) :
    BitVec n × BitVec n × StatusFlags :=
  let r := idivResult t d
  (r.1, r.2, { OF := u 0, SF := u 1, ZF := u 2, AF := u 3, PF := u 4, CF := u 5 })

theorem idiv_divFlags_allows {n : Nat} (u : Nat → Bool) (t : BitVec (n + n)) (d : BitVec n) :
    divFlags.Allows (idivSpec u t d).2.2 :=
  ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

open X86 X86.Helpers

theorem ofNat_concat_eq_append (k n : Nat) (x y : BitVec n) (hk : k = n + n) :
    (BitVec.ofNat k (x.toNat <<< n + y.toNat)).toInt = (x ++ y).toInt := by
  subst hk
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [toNat_ofNat_concat _ _ _ _ (Nat.le_refl _), toNat_append_eq]

theorem toInt_ne_zero {n : Nat} {x : BitVec n} (h : x ≠ 0) : x.toInt ≠ 0 := fun e =>
  h (BitVec.toInt_inj.mp (e.trans BitVec.toInt_zero.symm))

set_option hygiene false in
local macro "idiv_steps" rd:ident ra:ident wd:ident wa:ident fold:ident : tactic => `(tactic| (
  simp only [Operand.read_reg64, Operand.read_reg32, Operand.read_reg16] at hlo hhi ⊢
  unfold X86.Instructions.Operations.IDIV
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
  simp (disch := decide) only [ofNat_concat_eq_append, stdExp_two_eq_ok, liftM_ok]
  spec_bind_rfl
  spec_bind_rfl
  split
  · rename_i hc
    simp [HOr.hOr, OrOp.or, strictOr] at hc hlo hhi
    omega
  simp only [sliceInclusive_eq, x86_runtime, Int.pow_zero, Int.ediv_one]
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_with $wd _ _
  spec_bind_with $wa _ _
  rw [← $fold, ← $fold]
  simp only [Operand.write_write_setFlags]
  simp only [idivSpec, idivResult, Int.reduceToNat]
  generalize hT : (Operand.reg 0 : Operand _).write ((Operand.reg 2 : Operand _).write s _) _ = T
  have hTo : s.oracle = T.oracle := by subst hT; rfl
  repeat spec_bind_rfl
  rw [rflagsSetCF_run]
  dsimp only
  simp only [hTo]
  rw [setFlags_eq_of_store]
  · rfl
  · rflags_ext))

theorem idiv_operation {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ) (n : Nat)
    (hn : n = 16 ∨ n = 32 ∨ n = 64) (x : BitVec n)
    (h : IdivDefined ((Operand.reg 2 : Operand n).read s ++ (Operand.reg 0 : Operand n).read s) x) :
    (X86.Instructions.Operations.IDIV n x).run s =
      let r := idivSpec (fun i => oracleBit (oracleSkip s.oracle i))
        ((Operand.reg 2 : Operand n).read s ++ (Operand.reg 0 : Operand n).read s) x
      (.ok (), (Operand.reg 0 : Operand n).write ((Operand.reg 2 : Operand n).write
        (setFlags { s with oracle := oracleSkip s.oracle 6 } r.2.2) r.2.1) r.1) := by
  obtain ⟨hx, hlo, hhi⟩ := h
  have hxi : x.toInt ≠ 0 := toInt_ne_zero hx
  have hx0 : (x.toInt == 0) = false := by simpa using hxi
  rcases hn with rfl | rfl | rfl
  · idiv_steps dx_run ax_run dxWrite_run axWrite_run Operand.write_reg_eq_set
  · idiv_steps edx_run eax_run edxWrite_run eaxWrite_run Operand.write_reg_eq_set
  · idiv_steps rdx_run rax_run rdxWrite_run raxWrite_run Operand.write_reg64

theorem idiv_operation8 {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (x : BitVec 8) (h : IdivDefined ((Operand.reg 0 : Operand 16).read s) x) :
    (X86.Instructions.Operations.IDIV 8 x).run s =
      let r := idivSpec (fun i => oracleBit (oracleSkip s.oracle i))
        ((Operand.reg 0 : Operand 16).read s) x
      (.ok (), (Operand.reg 0 : Operand 16).write
        (setFlags { s with oracle := oracleSkip s.oracle 6 } r.2.2) (r.2.1 ++ r.1)) := by
  obtain ⟨hx, hlo, hhi⟩ := h
  have hxi : x.toInt ≠ 0 := toInt_ne_zero hx
  have hx0 : (x.toInt == 0) = false := by simpa using hxi
  simp only [Operand.read_reg16] at hlo hhi ⊢
  unfold X86.Instructions.Operations.IDIV
  simp only [x86_runtime]
  spec_bind_rfl
  spec_bind_with ax_run _
  spec_bind_rfl
  simp only [hx0, Bool.false_eq_true, ↓reduceIte, stdTruncatedDivide_eq_pure _ _ hxi,
    stdTruncatedRemainder_eq_pure _ _ hxi]
  spec_bind_rfl
  spec_bind_rfl
  simp (disch := decide) only [stdExp_two_eq_ok, liftM_ok]
  spec_bind_rfl
  spec_bind_rfl
  split
  · rename_i hc
    simp [HOr.hOr, OrOp.or, strictOr] at hc hlo hhi
    omega
  simp only [sliceInclusive_eq, x86_runtime, Int.pow_zero, Int.ediv_one]
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_with ahWrite_run _ _
  spec_bind_with alWrite_run _ _
  rw [← Operand.write_reg_eq_set, Operand.write_reg8_setSlice_high]
  simp only [Operand.write_setFlags]
  simp only [idivSpec, idivResult]
  generalize hT : (Operand.reg 0 : Operand 16).write s _ = T
  have hTo : s.oracle = T.oracle := by subst hT; rfl
  repeat spec_bind_rfl
  rw [rflagsSetCF_run]
  dsimp only
  simp only [hTo]
  rw [setFlags_eq_of_store]
  · rfl
  · rflags_ext

end X86Proofs
