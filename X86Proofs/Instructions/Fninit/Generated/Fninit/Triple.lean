
import X86Proofs.Instructions.Fninit.Generated.Fninit.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fninitEffect (p : BitVec 64) (len : Nat) :
    RamState → Effect := fun _ =>
  { rip := p + BitVec.ofNat 64 len
    writes := [
      ⟨(Operand.fcw : Operand 16), 0x037F⟩,
      ⟨(Operand.fsw : Operand 16), 0⟩,
      ⟨(Operand.fcc 15 : Operand 4), 0⟩,
      ⟨(Operand.ftw : Operand 16), 0xFFFF⟩,
      ⟨(Operand.fpuPtr : Operand 171), 0⟩] }

@[simp] theorem fninitEffect_components (p : BitVec 64) (len : Nat)
    (s : RamState) : (fninitEffect p len s).components = [.fcw, .fsw, .fcc, .ftw, .fpuPtr, .rip] :=
        rfl

theorem fninit_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p ∧ Prelude.CR0.SSEEnabled s.CR0) (codeRange p [0xDB, 0xE3])
      (fninitEffect p 2) := by
  rintro s h hcode ⟨hp, hcr0⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := fninit_step s h hcr0 [] (by simp) (by simp) rfl rfl 0xE3 (by decide) (by decide)
      (by decide)
    hcode.bytesAt hlow
  have hag := AgreesExcept.afterStep_x87Init s 2 (BitVec.add s.RIP (BitVec.ofNat 64 2))
    (fun t => fninitControl t.FP87_Control)
  refine ⟨_, hstep, h.of_agreesExcept hag h.memory.tables,
    ⟨afterStep_x87Init_rip h _ _ _, ?_, trivial, hag⟩⟩
  simp only [fninitEffect, Write.AllHold]
  simp only [Operand.read_afterStep]
  simp only [Operand.read_fcw, Operand.read_fsw, Operand.read_fcc, Operand.read_ftw,
    Operand.read_fpuPtr]
  refine ⟨fninitControl_eq _, ?_, ?_, rfl, ?_⟩ <;>
    simp [x87InitOut, fswRest, fswCC, fpuPtrOf]

theorem fninit_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => s.RIP = p ∧ Prelude.CR0.SSEEnabled s.CR0) (codeRange p [0xDB, 0xE3])
      (Effect.post (fninitEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fninitEffect_components]; simp [Component.Covers]) _)
    (fninit_effect_step p)

attribute [x86_compose] fninitEffect

@[x86_local] theorem fninitEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (fninitEffect p len) := by
  effect_local [fninitEffect]

end X86Proofs
