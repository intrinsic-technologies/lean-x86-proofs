
import X86Proofs.Instructions.Fnclex.Generated.Fnclex.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fnclexEffect (p : BitVec 64) (len : Nat) :
    RamState → Effect := fun s =>
  { rip := p + BitVec.ofNat 64 len
    writes := [
      ⟨(Operand.fsw : Operand 16), ((Operand.fsw : Operand 16).read s) &&& 0x3800#16⟩,
      ⟨(Operand.fcc 0 : Operand 4), 0⟩] }

@[simp] theorem fnclexEffect_components (p : BitVec 64) (len : Nat)
    (s : RamState) : (fnclexEffect p len s).components = [.fsw, .fcc, .rip] := rfl

theorem fnclex_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p ∧ Prelude.CR0.SSEEnabled s.CR0) (codeRange p [0xDB, 0xE2])
      (fnclexEffect p 2) := by
  rintro s h hcode ⟨hp, hcr0⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := fnclex_step s h hcr0 [] (by simp) (by simp) rfl rfl 0xE2 (by decide) (by decide)
      (by decide)
    hcode.bytesAt hlow
  have hag := AgreesExcept.afterStep_x87Ctl s 2 (BitVec.add s.RIP (BitVec.ofNat 64 2))
    4 (fun t => fnclexStatus t.FP87_Status t.oracle)
  refine ⟨_, hstep, h.of_agreesExcept hag h.memory.tables,
    ⟨afterStep_x87Ctl_rip h _ _ _ _, ?_, trivial, hag⟩⟩
  simp only [fnclexEffect, Write.AllHold, Operand.read_fsw, Operand.read_fcc,
    fswRest_and_3800]
  exact ⟨fswRest_fnclexStatus _ _, BitVec.and_zero⟩

theorem fnclex_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => s.RIP = p ∧ Prelude.CR0.SSEEnabled s.CR0) (codeRange p [0xDB, 0xE2])
      (Effect.post (fnclexEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fnclexEffect_components]; simp [Component.Covers]) _)
    (fnclex_effect_step p)

attribute [x86_compose] fnclexEffect

@[x86_local] theorem fnclexEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (fnclexEffect p len) := by
  effect_local [fnclexEffect]

end X86Proofs
