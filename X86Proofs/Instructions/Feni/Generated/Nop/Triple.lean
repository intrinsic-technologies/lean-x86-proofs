
import X86Proofs.Instructions.Feni.Generated.Nop.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Nop.Step

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def feniEffect (p : BitVec 64) (len : Nat) :
    RamState → Effect := fun _ =>
  { rip := p + BitVec.ofNat 64 len
    writes := [] }

@[simp] theorem feniEffect_components (p : BitVec 64) (len : Nat)
    (s : RamState) : (feniEffect p len s).components = [.rip] := rfl

theorem feni_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p ∧ Prelude.CR0.SSEEnabled s.CR0) (codeRange p [0xDB, 0xE0])
      (feniEffect p 2) := by
  rintro s h hcode ⟨hp, hcr0⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := feni_step s h hcr0 [] (by simp) (by simp) rfl rfl 0xE0 (by decide) (by decide)
      (by decide)
    hcode.bytesAt hlow
  exact ⟨_, hstep, ReadyToStep.afterStep_withNextIP h 2 _,
    ⟨afterStep_withNextIP_rip h 2 _, trivial, trivial,
      AgreesExcept.afterStep_withNextIP s 2 _⟩⟩

theorem feni_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => s.RIP = p ∧ Prelude.CR0.SSEEnabled s.CR0) (codeRange p [0xDB, 0xE0])
      (Effect.post (feniEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [feniEffect_components]; simp [Component.Covers]) _)
    (feni_effect_step p)

attribute [x86_compose] feniEffect

@[x86_local] theorem feniEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (feniEffect p len) := by
  effect_local [feniEffect]

end X86Proofs
