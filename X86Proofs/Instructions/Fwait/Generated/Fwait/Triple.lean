
import X86Proofs.Instructions.Fwait.Generated.Fwait.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fwaitEffect (p : BitVec 64) (len : Nat) :
    RamState → Effect := fun _ =>
  { rip := p + BitVec.ofNat 64 len
    writes := [
      ⟨(Operand.fcc 0 : Operand 4), 0⟩] }

@[simp] theorem fwaitEffect_components (p : BitVec 64) (len : Nat)
    (s : RamState) : (fwaitEffect p len s).components = [.fcc, .rip] := rfl

theorem fwait_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p ∧ Prelude.CR0.SSEEnabled s.CR0 ∧ fswES s.FP87_Status = 0)
        (codeRange p [0x9B])
      (fwaitEffect p 1) := by
  rintro s h hcode ⟨hp, hcr0, hes⟩
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := fwait_step s h hcr0 hes [] (by simp) (by simp) rfl rfl
    hcode.bytesAt hlow
  have hag := AgreesExcept.afterStep_x87Ctl_cc s 1 (BitVec.add s.RIP (BitVec.ofNat 64 1))
    4 (fun t => fswCCOracle t.FP87_Status t.oracle) (fswRest_fswCCOracle _ _)
  refine ⟨_, hstep, h.of_agreesExcept hag h.memory.tables,
    ⟨afterStep_x87Ctl_rip h _ _ _ _, ?_, trivial, hag⟩⟩
  simp only [fwaitEffect, Write.AllHold, Operand.read_fcc]
  exact BitVec.and_zero

theorem fwait_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => s.RIP = p ∧ Prelude.CR0.SSEEnabled s.CR0 ∧ fswES s.FP87_Status = 0)
        (codeRange p [0x9B])
      (Effect.post (fwaitEffect p 1)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fwaitEffect_components]; simp [Component.Covers]) _)
    (fwait_effect_step p)

attribute [x86_compose] fwaitEffect

@[x86_local] theorem fwaitEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (fwaitEffect p len) := by
  effect_local [fwaitEffect]

end X86Proofs
