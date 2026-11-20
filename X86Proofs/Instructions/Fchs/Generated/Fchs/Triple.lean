
import X86Proofs.Instructions.Fchs.Generated.Fchs.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fchsEffect (p : BitVec 64) (len : Nat) (top : BitVec 3) (s : RamState) : Effect :=
  x87Effect p len [(top, fchsSpec ((Operand.fpr (top) : Operand 80).read s))]
    (ftwSet ((Operand.ftw : Operand 16).read s) top
        (x87Tag (fchsSpec ((Operand.fpr (top) : Operand 80).read s))))
    (((Operand.fsw : Operand 16).read s)) (2) (0) s

@[simp] theorem fchsEffect_components (p : BitVec 64) (len : Nat) (top : BitVec 3) (s : RamState) :
    (fchsEffect p len top s).components = [.fpr (top), .ftw, .fsw, .fcc, .fpuPtr, .rip] := rfl

theorem fchs_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) :
    StepEffect (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3)
      (codeRange p [0xD9, 0xE0]) (fchsEffect p 2 top) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, h0⟩
  subst hp htop
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := fchs_step s h hcr0 hes hm hfdp [] (by simp) (by simp) rfl rfl 0xE0 (by decide)
    (by decide) (by decide) h0 hcode.bytesAt hlow
  have hh : (fchsEffect s.RIP 2 (fswTop s.FP87_Status) s).Holds s _ :=
    x87Effect_holds h 2 s.RIP rfl (fun t => 6) _
      (fun t => fprSet t.FP87 (fswTop t.FP87_Status)
          (fchsSpec t.FP87[fprIndex (fswTop t.FP87_Status)]))
      (fun t => ftwSet t.FP87_Tag_Word (fswTop t.FP87_Status)
          (x87Tag (fchsSpec t.FP87[fprIndex (fswTop t.FP87_Status)])))
      (fun t => x87UnaryStatus t.FP87_Status t.oracle) _ _ _ _
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
        simp only [Operand.read_fsw, x87UnaryStatus_eq, fswRest_fswC1Zero]
        rfl)
      (by
        rw [x87UnaryStatus_eq]
        exact fswCC_fswC1Zero _ _)
  exact ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩

theorem fchs_triple [Bindings] (p : BitVec 64) (top : BitVec 3) :
    Triple (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3)
      (codeRange p [0xD9, 0xE0]) (Effect.post (fchsEffect p 2 top)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fchsEffect_components]; simp [Component.Covers]) _)
    (fchs_effect_step p top)

attribute [x86_compose] fchsEffect

@[x86_local] theorem fchsEffect_local {p : BitVec 64} {len : Nat} {top : BitVec 3} :
    Effect.Local (fchsEffect p len top) := by
  effect_local [fchsEffect, x87Effect]

end X86Proofs
