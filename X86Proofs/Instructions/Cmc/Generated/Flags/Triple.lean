
import X86Proofs.Instructions.Cmc.Generated.Flags.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cmcEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    flags := some (.ofStatusFlags (cmcSpec (StatusFlags.ofRFLAGS s.RFLAGS))) }

@[simp] theorem cmcEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (cmcEffect p len s).components = [.flags, .rip] := rfl

theorem cmc_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0xF5]) (cmcEffect p 1) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cmc_step s h [] (by simp) (by simp) rfl rfl hcode.bytesAt hlow
  exact ⟨_, hstep, ReadyToStep.afterStep_writeFlagsOutputs h _ _ _ _,
    ⟨afterStep_writeFlagsOutputs_rip h _ _ _ _, trivial,
      StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _,
      AgreesExcept.afterStep_writeFlagsOutputs s _ _ _ _⟩⟩

theorem cmc_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => s.RIP = p) (codeRange p [0xF5]) (Effect.post (cmcEffect p 1)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmcEffect_components]; simp [Component.Covers]) _)
    (cmc_effect_step p)

attribute [x86_compose] cmcEffect

@[x86_local] theorem cmcEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (cmcEffect p len) := by
  effect_local [cmcEffect, cmcSpec]

end X86Proofs
