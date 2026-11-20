
import X86Proofs.Instructions.Fld1.Generated.Fld1.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fld1Effect (p : BitVec 64) (len : Nat) (top : BitVec 3) (s : RamState) : Effect :=
  x87Effect p len [(top - 1, x87Const 0 (fcwRC ((Operand.fcw : Operand 16).read s)))]
    (ftwSet ((Operand.ftw : Operand 16).read s) (top - 1)
        (x87Tag (x87Const 0 (fcwRC ((Operand.fcw : Operand 16).read s)))))
    (fswSetTop ((Operand.fsw : Operand 16).read s) (top - 1)) (2) (0) s

@[simp] theorem fld1Effect_components (p : BitVec 64) (len : Nat) (top : BitVec 3) (s : RamState) :
    (fld1Effect p len top s).components = [.fpr (top - 1), .ftw, .fsw, .fcc, .fpuPtr, .rip] := rfl

theorem fld1_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) :
    StepEffect (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top + 7) = 3)
      (codeRange p [0xD9, 0xE8]) (fld1Effect p 2 top) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, hpush⟩
  subst hp htop
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := fld1_step s h hcr0 hes hm hfdp [] (by simp) (by simp) rfl rfl 0xE8 (by decide)
    (by decide) (by decide) hpush hcode.bytesAt hlow
  have hh : (fld1Effect s.RIP 2 (fswTop s.FP87_Status) s).Holds s _ :=
    x87Effect_holds h 2 s.RIP rfl (fun t => 3) _
      (fun t => fprSet t.FP87 (fswTop t.FP87_Status - 1) (x87Const 0 (fcwRC t.FP87_Control)))
      (fun t => ftwSet t.FP87_Tag_Word (fswTop t.FP87_Status - 1)
          (x87Tag (x87Const 0 (fcwRC t.FP87_Control))))
      (fun t => fswSetTop (fldStatus t.FP87_Status t.oracle) (fswTop t.FP87_Status - 1)) _ _ _ _
      (by
        intro rv hrv
        simp only [List.mem_singleton] at hrv
        subst hrv
        exact fprSet_get_self _ _ _)
      (by
        intro r hr
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr
        exact fprSet_get_of_ne _ (Ne.symm hr) _)
      (by
        x87_simp)
      (by
        simp only [Operand.read_fsw, fswRest_fswSetTop, fswRest_fldStatus]
        rfl)
      (by
        simp only [fswCC_fswSetTop]
        exact fswCC_fldStatus_c1 _ _)
  exact ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩

theorem fld1_triple [Bindings] (p : BitVec 64) (top : BitVec 3) :
    Triple (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top + 7) = 3)
      (codeRange p [0xD9, 0xE8]) (Effect.post (fld1Effect p 2 top)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fld1Effect_components]; simp [Component.Covers]) _)
    (fld1_effect_step p top)

attribute [x86_compose] fld1Effect

@[x86_local] theorem fld1Effect_local {p : BitVec 64} {len : Nat} {top : BitVec 3} :
    Effect.Local (fld1Effect p len top) := by
  effect_local [fld1Effect, x87Effect]

end X86Proofs
