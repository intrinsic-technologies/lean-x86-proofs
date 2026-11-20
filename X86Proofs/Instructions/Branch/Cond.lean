import X86Proofs.Core.Flags
import X86Proofs.Core.Run

/-!
# Branch conditions

A conditional jump `Jcc` (`70+cc rel8`, `0F 80+cc rel32`) branches if condition `cc` (the low four
bits of the opcode) holds of the status flags. `condHolds cc f` is that condition, written as the
SDM's table (bit 0 of `cc` negates the condition of `cc` with bit 0 clear):

| `cc` | Jcc | condition |
|---|---|---|
| 0 / 1 | JO / JNO | OF / ¬OF |
| 2 / 3 | JB / JAE (JNB) | CF / ¬CF |
| 4 / 5 | JE (JZ) / JNE (JNZ) | ZF / ¬ZF |
| 6 / 7 | JBE / JA (JNBE) | CF ∨ ZF / ¬(CF ∨ ZF) |
| 8 / 9 | JS / JNS | SF / ¬SF |
| A / B | JP / JNP | PF / ¬PF |
| C / D | JL / JGE (JNL) | SF ≠ OF / SF = OF |
| E / F | JLE / JG (JNLE) | ZF ∨ SF ≠ OF / ¬(ZF ∨ SF ≠ OF) |

`conditionHolds_run`: lean-x86's `Condition_Holds cc` returns `condHolds cc` of the status flags
in RFLAGS (`StatusFlags.ofRFLAGS`) and leaves the state alone. For a literal `cc`, `condHolds cc f`
reduces by `rfl` (e.g. `condHolds 4 f = f.ZF`), and `condHolds_0`, …, `condHolds_15` state each case
as a rewrite.
-/

namespace X86Proofs

open X86 X86.Helpers

/-- Condition `cc` of the status flags `f` (the SDM's `Jcc`/`SETcc`/`CMOVcc` table). -/
def condHolds (cc : BitVec 4) (f : StatusFlags) : Bool :=
  match cc.toNat with
  | 0 => f.OF
  | 1 => !f.OF
  | 2 => f.CF
  | 3 => !f.CF
  | 4 => f.ZF
  | 5 => !f.ZF
  | 6 => f.CF || f.ZF
  | 7 => !(f.CF || f.ZF)
  | 8 => f.SF
  | 9 => !f.SF
  | 10 => f.PF
  | 11 => !f.PF
  | 12 => f.SF != f.OF
  | 13 => f.SF == f.OF
  | 14 => f.ZF || f.SF != f.OF
  | _ => !(f.ZF || f.SF != f.OF)

/-! A condition of a literal code as the flags it reads, `condHolds`'s cases (`condHolds 15 f` is
`!(f.ZF || f.SF != f.OF)`). Proved by cases rather than `rfl`, so that none is a `dsimp` lemma (an
`if`'s `Decidable` instance would keep the term rewritten). -/

section Conditions

variable (f : StatusFlags)

theorem condHolds_0 : condHolds 0 f = f.OF := by cases f; rfl
theorem condHolds_1 : condHolds 1 f = !f.OF := by cases f; rfl
theorem condHolds_2 : condHolds 2 f = f.CF := by cases f; rfl
theorem condHolds_3 : condHolds 3 f = !f.CF := by cases f; rfl
theorem condHolds_4 : condHolds 4 f = f.ZF := by cases f; rfl
theorem condHolds_5 : condHolds 5 f = !f.ZF := by cases f; rfl
theorem condHolds_6 : condHolds 6 f = (f.CF || f.ZF) := by cases f; rfl
theorem condHolds_7 : condHolds 7 f = !(f.CF || f.ZF) := by cases f; rfl
theorem condHolds_8 : condHolds 8 f = f.SF := by cases f; rfl
theorem condHolds_9 : condHolds 9 f = !f.SF := by cases f; rfl
theorem condHolds_10 : condHolds 10 f = f.PF := by cases f; rfl
theorem condHolds_11 : condHolds 11 f = !f.PF := by cases f; rfl
theorem condHolds_12 : condHolds 12 f = (f.SF != f.OF) := by cases f; rfl
theorem condHolds_13 : condHolds 13 f = (f.SF == f.OF) := by cases f; rfl
theorem condHolds_14 : condHolds 14 f = (f.ZF || f.SF != f.OF) := by cases f; rfl
theorem condHolds_15 : condHolds 15 f = !(f.ZF || f.SF != f.OF) := by cases f; rfl

end Conditions

/-- `Condition_Holds` as lean-x86 computes it, on the RFLAGS bits (an intermediate for
`conditionHolds_run`, equal to it by `rfl` for each literal `cc`). -/
def conditionBits (r : BitVec 64) (cc : BitVec 4) : Bool :=
  let base := match cc.toNat / 2 with
    | 0 => r.extractLsb' 11 1 == 1
    | 1 => r.extractLsb' 0 1 == 1
    | 2 => r.extractLsb' 6 1 == 1
    | 3 => r.extractLsb' 0 1 == 1 || r.extractLsb' 6 1 == 1
    | 4 => r.extractLsb' 7 1 == 1
    | 5 => r.extractLsb' 2 1 == 1
    | 6 => r.extractLsb' 7 1 != r.extractLsb' 11 1
    | _ => r.extractLsb' 6 1 == 1 || r.extractLsb' 7 1 != r.extractLsb' 11 1
  if cc.toNat % 2 = 0 then base else !base

theorem conditionHolds_run_fin {σ : Type} (s : X86.State σ) (index : Fin 16) :
    (Condition_Holds (BitVec.ofNat 4 index.val)).run s =
      (.ok (conditionBits s.RFLAGS (BitVec.ofNat 4 index.val)), s) := by
  finite_cases index <;> rfl

theorem extractLsb'_one_eq_ofBool {w : Nat} (r : BitVec w) (k : Nat) :
    r.extractLsb' k 1 = BitVec.ofBool (r.getLsbD k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have : i = 0 := by omega
  subst this
  simp

theorem extractLsb'_one_beq {w : Nat} (r : BitVec w) (k : Nat) :
    (r.extractLsb' k 1 == 1#1) = r.getLsbD k := by
  rw [extractLsb'_one_eq_ofBool]
  cases r.getLsbD k <;> decide

theorem extractLsb'_one_bne {w : Nat} (r : BitVec w) (j k : Nat) :
    (r.extractLsb' j 1 != r.extractLsb' k 1) = (r.getLsbD j != r.getLsbD k) := by
  rw [extractLsb'_one_eq_ofBool, extractLsb'_one_eq_ofBool]
  cases r.getLsbD j <;> cases r.getLsbD k <;> decide

theorem conditionBits_eq (r : BitVec 64) (cc : BitVec 4) :
    conditionBits r cc = condHolds cc (StatusFlags.ofRFLAGS r) := by
  have : cc ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := by
    revert cc
    decide
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;>
  simp [conditionBits, condHolds, StatusFlags.ofRFLAGS, extractLsb'_one_beq, extractLsb'_one_bne]
  all_goals (generalize r[7] = a; generalize r[11] = b; revert a b; decide)

/-- lean-x86's branch condition: `Condition_Holds cc` returns `condHolds cc` of the status flags
and leaves the state alone. -/
theorem conditionHolds_run {σ : Type} (s : X86.State σ) (cc : BitVec 4) :
    (Condition_Holds cc).run s = (.ok (condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS)), s) := by
  rw [← conditionBits_eq]
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    conditionHolds_run_fin s ⟨cc.toNat, cc.isLt⟩

end X86Proofs
