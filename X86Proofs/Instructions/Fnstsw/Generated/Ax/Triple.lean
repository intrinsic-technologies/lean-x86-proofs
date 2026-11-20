
import X86Proofs.Instructions.Fnstsw.Generated.Ax.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fnstswAxEffect (p : BitVec 64) (len : Nat) (cc : BitVec 4) :
    RamState → Effect := fun s =>
  { rip := p + BitVec.ofNat 64 len
    writes := [
      ⟨(Operand.reg 0 : Operand 64), mergeGPR 16 (((Operand.fsw : Operand 16).read s) ||| ccWord cc)
          ((Operand.reg 0 : Operand 64).read s)⟩,
      ⟨(Operand.fcc 0 : Operand 4), 0⟩] }

@[simp] theorem fnstswAxEffect_components (p : BitVec 64) (len : Nat) (cc : BitVec 4)
    (s : RamState) : (fnstswAxEffect p len cc s).components = [.reg 0, .fcc, .rip] := rfl

theorem fnstsw_ax_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) :
    StepEffect (fun s => s.RIP = p ∧ Prelude.CR0.SSEEnabled s.CR0 ∧ fswCC s.FP87_Status = cc)
        (codeRange p [0xDF, 0xE0])
      (fnstswAxEffect p 2 cc) := by
  rintro s h hcode ⟨hp, hcr0, hcc⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := fnstsw_ax_step s h hcr0 [] (by simp) (by simp) rfl rfl 0xE0 (by decide) (by decide)
      (by decide)
    hcode.bytesAt hlow
  have hag := AgreesExcept.afterStep_x87Stsw s 2 (BitVec.add s.RIP (BitVec.ofNat 64 2))
    4 (fun t => fswCCOracle t.FP87_Status t.oracle) (fun t => t.FP87_Status)
        (fswRest_fswCCOracle _ _)
  refine ⟨_, hstep, h.of_agreesExcept hag h.memory.tables,
    ⟨afterStep_x87Stsw_rip h _ _ _ _ _, ?_, trivial, hag⟩⟩
  subst hcc
  simp only [fnstswAxEffect, Write.AllHold, Operand.read_afterStep,
    Operand.read_reg64_write_reg16, Operand.read_fsw, Operand.read_fcc, fswRest_or_ccWord]
  exact ⟨rfl, BitVec.and_zero⟩

theorem fnstsw_ax_triple [Bindings] (p : BitVec 64) (cc : BitVec 4) :
    Triple (fun s => s.RIP = p ∧ Prelude.CR0.SSEEnabled s.CR0 ∧ fswCC s.FP87_Status = cc)
        (codeRange p [0xDF, 0xE0])
      (Effect.post (fnstswAxEffect p 2 cc)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fnstswAxEffect_components]; simp [Component.Covers]) _)
    (fnstsw_ax_effect_step p cc)

attribute [x86_compose] fnstswAxEffect

@[x86_local] theorem fnstswAxEffect_local {p : BitVec 64} {len : Nat} {cc : BitVec 4} :
    Effect.Local (fnstswAxEffect p len cc) := by
  effect_local [fnstswAxEffect]

end X86Proofs
