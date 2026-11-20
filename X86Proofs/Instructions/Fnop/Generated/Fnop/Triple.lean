
import X86Proofs.Instructions.Fnop.Generated.Fnop.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fnopEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect :=
  x87Effect p len []
    (((Operand.ftw : Operand 16).read s))
    (((Operand.fsw : Operand 16).read s)) (0) (0) s

@[simp] theorem fnopEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (fnopEffect p len s).components = [.ftw, .fsw, .fcc, .fpuPtr, .rip] := rfl

theorem fnop_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) :
    StepEffect (fun s => X87Pre p top s)
      (codeRange p [0xD9, 0xD0]) (fnopEffect p 2) := by
  rintro s h hcode ⟨hp, hcr0, hes, _, hfdp, htop⟩
  subst hp htop
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := fnop_step s h hcr0 hes hfdp [] (by simp) (by simp) rfl rfl 0xD0 (by decide)
    (by decide) (by decide) hcode.bytesAt hlow
  have hh : (fnopEffect s.RIP 2 s).Holds s _ :=
    x87Effect_holds h 2 s.RIP rfl (fun t => 4) _
      (fun t => t.FP87)
      (fun t => t.FP87_Tag_Word)
      (fun t => fswCCOracle t.FP87_Status t.oracle) _ _ _ _
      (fun _ h => absurd h List.not_mem_nil)
      (fun _ _ => rfl)
      (by
        x87_simp)
      (by
        simp only [Operand.read_fsw, fswRest_fswCCOracle]
        rfl)
      (by
        exact BitVec.and_zero)
  exact ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩

theorem fnop_triple [Bindings] (p : BitVec 64) (top : BitVec 3) :
    Triple (fun s => X87Pre p top s)
      (codeRange p [0xD9, 0xD0]) (Effect.post (fnopEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fnopEffect_components]; simp [Component.Covers]) _)
    (fnop_effect_step p top)

attribute [x86_compose] fnopEffect

@[x86_local] theorem fnopEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (fnopEffect p len) := by
  effect_local [fnopEffect, x87Effect]

end X86Proofs
