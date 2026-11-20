
import X86Proofs.Instructions.Fdecstp.Generated.Fdecstp.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fdecstpEffect (p : BitVec 64) (len : Nat) (top : BitVec 3) (s : RamState) : Effect :=
  x87Effect p len []
    (((Operand.ftw : Operand 16).read s))
    (fswSetTop ((Operand.fsw : Operand 16).read s) (top - 1)) (2) (0) s

@[simp] theorem fdecstpEffect_components (p : BitVec 64) (len : Nat) (top : BitVec 3) (s : RamState)
    :
    (fdecstpEffect p len top s).components = [.ftw, .fsw, .fcc, .fpuPtr, .rip] := rfl

theorem fdecstp_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) :
    StepEffect (fun s => X87Pre p top s)
      (codeRange p [0xD9, 0xF6]) (fdecstpEffect p 2 top) := by
  rintro s h hcode ⟨hp, hcr0, hes, _, hfdp, htop⟩
  subst hp htop
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := fdecstp_step s h hcr0 hes hfdp [] (by simp) (by simp) rfl rfl 0xF6 (by decide)
    (by decide) (by decide) hcode.bytesAt hlow
  have hh : (fdecstpEffect s.RIP 2 (fswTop s.FP87_Status) s).Holds s _ :=
    x87Effect_holds h 2 s.RIP rfl (fun t => 3) _
      (fun t => t.FP87)
      (fun t => t.FP87_Tag_Word)
      (fun t => fswSetTop (fswC1Zero t.FP87_Status t.oracle)
          (fswTop (fswC1Zero t.FP87_Status t.oracle) - 1)) _ _ _ _
      (fun _ h => absurd h List.not_mem_nil)
      (fun _ _ => rfl)
      (by
        x87_simp)
      (by
        simp only [Operand.read_fsw, fswRest_fswSetTop, fswRest_fswC1Zero, fswTop_fswC1Zero]
        rfl)
      (by
        simp only [fswCC_fswSetTop]
        exact fswCC_fswC1Zero _ _)
  exact ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩

theorem fdecstp_triple [Bindings] (p : BitVec 64) (top : BitVec 3) :
    Triple (fun s => X87Pre p top s)
      (codeRange p [0xD9, 0xF6]) (Effect.post (fdecstpEffect p 2 top)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fdecstpEffect_components]; simp [Component.Covers]) _)
    (fdecstp_effect_step p top)

attribute [x86_compose] fdecstpEffect

@[x86_local] theorem fdecstpEffect_local {p : BitVec 64} {len : Nat} {top : BitVec 3} :
    Effect.Local (fdecstpEffect p len top) := by
  effect_local [fdecstpEffect, x87Effect]

end X86Proofs
