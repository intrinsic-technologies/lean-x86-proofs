
import X86Proofs.Instructions.Fxtract.Generated.Fxtract.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fxtractEffect (p : BitVec 64) (len : Nat) (top : BitVec 3) (s : RamState) : Effect :=
  x87Effect p len
      [(top, (x87Extract ((Operand.fpr (top) : Operand 80).read s)).2.1),
      (top - 1, (x87Extract ((Operand.fpr (top) : Operand 80).read s)).1)]
    (ftwSet
        (ftwSet ((Operand.ftw : Operand 16).read s) top
        (x87Tag (x87Extract ((Operand.fpr (top) : Operand 80).read s)).2.1)) (top - 1)
        (x87Tag (x87Extract ((Operand.fpr (top) : Operand 80).read s)).1))
    (fswSetTop
        (fswOrFlags ((Operand.fsw : Operand 16).read s)
        (x87Extract ((Operand.fpr (top) : Operand 80).read s)).2.2) (top - 1)) (2) (0) s

@[simp] theorem fxtractEffect_components (p : BitVec 64) (len : Nat) (top : BitVec 3) (s : RamState)
    :
    (fxtractEffect p len top s).components =
        [.fpr (top), .fpr (top - 1), .ftw, .fsw, .fcc, .fpuPtr, .rip] := rfl

theorem fxtract_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) :
    StepEffect
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ ftwTag s.FP87_Tag_Word
        (top + 7) = 3 ∧ X87ExtractOk s.FP87[fprIndex (top)])
      (codeRange p [0xD9, 0xF4]) (fxtractEffect p 2 top) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, h0, hpush, hok⟩
  subst hp htop
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := fxtract_step s h hcr0 hes hm hfdp [] (by simp) (by simp) rfl rfl 0xF4 (by decide)
    (by decide) (by decide) h0 hpush hok hcode.bytesAt hlow
  have hh : (fxtractEffect s.RIP 2 (fswTop s.FP87_Status) s).Holds s _ :=
    x87Effect_holds h 2 s.RIP rfl (fun t => 6) _
      (fun t => fprSet
          (fprSet t.FP87 (fswTop t.FP87_Status)
          (x87Extract t.FP87[fprIndex (fswTop t.FP87_Status)]).2.1) (fswTop t.FP87_Status - 1)
          (x87Extract t.FP87[fprIndex (fswTop t.FP87_Status)]).1)
      (fun t => ftwSet
          (ftwSet t.FP87_Tag_Word (fswTop t.FP87_Status)
          (x87Tag (x87Extract t.FP87[fprIndex (fswTop t.FP87_Status)]).2.1))
          (fswTop t.FP87_Status - 1)
          (x87Tag (x87Extract t.FP87[fprIndex (fswTop t.FP87_Status)]).1))
      (fun t => x87ExtractFsw (fswSetTop t.FP87_Status (fswTop t.FP87_Status - 1)) t.FP87_Status
          t.oracle (x87Extract t.FP87[fprIndex (fswTop t.FP87_Status)]).2.2) _ _ _ _
      (by
        intro rv hrv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hrv
        rcases hrv with rfl | rfl
        · x87_simp
          rw [fprSet_get_of_ne _ (sub_one_ne3 _)]
          exact fprSet_get_self _ _ _
        · x87_simp)
      (by
        intro r hr
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
          not_or] at hr
        exact (fprSet_get_of_ne _ (Ne.symm hr.2) _).trans
          (fprSet_get_of_ne _ (Ne.symm hr.1) _))
      (by
        x87_simp)
      (by
        simp only [Operand.read_fsw, fswRest_x87ExtractFsw_top]
        rfl)
      (by
        exact fswCC_x87ExtractFsw _ _ _ _)
  exact ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩

theorem fxtract_triple [Bindings] (p : BitVec 64) (top : BitVec 3) :
    Triple
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ ftwTag s.FP87_Tag_Word
        (top + 7) = 3 ∧ X87ExtractOk s.FP87[fprIndex (top)])
      (codeRange p [0xD9, 0xF4]) (Effect.post (fxtractEffect p 2 top)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fxtractEffect_components]; simp [Component.Covers]) _)
    (fxtract_effect_step p top)

attribute [x86_compose] fxtractEffect

@[x86_local] theorem fxtractEffect_local {p : BitVec 64} {len : Nat} {top : BitVec 3} :
    Effect.Local (fxtractEffect p len top) := by
  effect_local [fxtractEffect, x87Effect]

end X86Proofs
