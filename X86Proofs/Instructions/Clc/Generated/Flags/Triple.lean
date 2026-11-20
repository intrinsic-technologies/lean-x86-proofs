
import X86Proofs.Instructions.Clc.Generated.Flags.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def clcEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    flags := some (.ofStatusFlags (clcSpec (StatusFlags.ofRFLAGS s.RFLAGS))) }

@[simp] theorem clcEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (clcEffect p len s).components = [.flags, .rip] := rfl

theorem clc_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xF8]) (clcEffect p 1) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := clc_step s h [] (by simp) (by simp) rfl rfl hcode.bytesAt hlow
  exact ⟨_, hstep, ReadyToStep.afterStep_writeFlagsOutputs h _ _ _ _,
    ⟨afterStep_writeFlagsOutputs_rip h _ _ _ _, trivial,
      StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _,
      AgreesExcept.afterStep_writeFlagsOutputs s _ _ _ _⟩⟩

theorem clc_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => s.RIP = p) (codeRange p [0xF8]) (Effect.post (clcEffect p 1)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [clcEffect_components]; simp [Component.Covers]) _)
    (clc_effect_step p)

attribute [x86_compose] clcEffect

@[x86_local] theorem clcEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (clcEffect p len) := by
  effect_local [clcEffect, clcSpec]

end X86Proofs
