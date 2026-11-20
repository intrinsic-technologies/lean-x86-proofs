import X86Proofs.Instructions.Emms.Generated.Emms.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def emmsEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.fsw : Operand 16), mmxStatus ((Operand.fsw : Operand 16).read s)⟩,
      ⟨(Operand.ftw : Operand 16), emmsSpec⟩] }

@[simp] theorem emmsEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (emmsEffect p len s).components = [.fsw, .ftw, .rip] := rfl

theorem emms_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (MmxPre p) (codeRange p [0x0F, 0x77]) (emmsEffect p 2) := by
  rintro s h hcode ⟨hp, hcr0, hes, hmmx⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := emms_step s h hcr0 hes hmmx [] (by simp) (by simp) rfl rfl rfl rfl
    hcode.bytesAt hlow
  have hag := AgreesExcept.afterStep_fsw_ftw s 2 (fun t => mmxStatus t.FP87_Status)
    (fun _ => emmsSpec) (BitVec.add s.RIP (BitVec.ofNat 64 2)) (fun _ => fswCC_mmxStatus _)
  exact ⟨_, hstep, h.of_agreesExcept hag h.memory.tables,
    ⟨afterStep_fsw_ftw_rip h _ _ _ _, ⟨fswRest_mmxStatus _, rfl⟩, trivial, hag⟩⟩

theorem emms_triple [Bindings] (p : BitVec 64) :
    Triple (MmxPre p) (codeRange p [0x0F, 0x77]) (Effect.post (emmsEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [emmsEffect_components]; simp [Component.Covers]) _)
    (emms_effect_step p)

attribute [x86_compose] emmsEffect

@[x86_local] theorem emmsEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (emmsEffect p len) := by
  effect_local [emmsEffect]

end X86Proofs
