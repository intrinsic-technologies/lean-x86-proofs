
import X86Proofs.Instructions.Fxam.Generated.Fxam.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fxamEffect (p : BitVec 64) (len : Nat) (top : BitVec 3) (s : RamState) : Effect :=
  x87Effect p len []
    (((Operand.ftw : Operand 16).read s))
    (((Operand.fsw : Operand 16).read s)) (15)
        (fxamCC (ftwTag ((Operand.ftw : Operand 16).read s) top == 3)
        ((Operand.fpr (top) : Operand 80).read s)) s

@[simp] theorem fxamEffect_components (p : BitVec 64) (len : Nat) (top : BitVec 3) (s : RamState) :
    (fxamEffect p len top s).components = [.ftw, .fsw, .fcc, .fpuPtr, .rip] := rfl

theorem fxam_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) :
    StepEffect (fun s => X87Pre p top s)
      (codeRange p [0xD9, 0xE5]) (fxamEffect p 2 top) := by
  rintro s h hcode ⟨hp, hcr0, hes, _, hfdp, htop⟩
  subst hp htop
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := fxam_step s h hcr0 hes hfdp [] (by simp) (by simp) rfl rfl 0xE5 (by decide)
    (by decide) (by decide) hcode.bytesAt hlow
  have hh : (fxamEffect s.RIP 2 (fswTop s.FP87_Status) s).Holds s _ :=
    x87Effect_holds h 2 s.RIP rfl (fun t => 0) _
      (fun t => t.FP87)
      (fun t => t.FP87_Tag_Word)
      (fun t => fxamStatus t.FP87_Status (ftwTag t.FP87_Tag_Word (fswTop t.FP87_Status) == 3)
          t.FP87[fprIndex (fswTop t.FP87_Status)]) _ _ _ _
      (fun _ h => absurd h List.not_mem_nil)
      (fun _ _ => rfl)
      (by
        x87_simp)
      (by
        simp only [Operand.read_fsw, fswRest_fxamStatus]
        rfl)
      (by
        rw [fswCC_fxamStatus, cc_and_15]
        rfl)
  exact ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩

theorem fxam_triple [Bindings] (p : BitVec 64) (top : BitVec 3) :
    Triple (fun s => X87Pre p top s)
      (codeRange p [0xD9, 0xE5]) (Effect.post (fxamEffect p 2 top)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fxamEffect_components]; simp [Component.Covers]) _)
    (fxam_effect_step p top)

attribute [x86_compose] fxamEffect

@[x86_local] theorem fxamEffect_local {p : BitVec 64} {len : Nat} {top : BitVec 3} :
    Effect.Local (fxamEffect p len top) := by
  effect_local [fxamEffect, x87Effect]

end X86Proofs
