import X86Proofs.Instructions.Nop.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

/-!
# NOP triples

The effect of a NOP of `len` bytes at `p` is `nopEffect p len`: RIP = `p + len`, no writes, flags
untouched; only RIP changes.
- `nop_triple`: `90`.
- `nop_66_triple`: `66 90`.
- `nop_r_triple`: `0F 1F /0` with a register operand, for any such ModRM byte.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- The effect of a NOP of `len` bytes at `p`: RIP = `p + len`, nothing else. -/
def nopEffect (p : BitVec 64) (len : Nat) : Effect :=
  { rip := p + BitVec.ofNat 64 len }

/-- A NOP changes only RIP. -/
@[simp] theorem nopEffect_components (p : BitVec 64) (len : Nat) :
    (nopEffect p len).components = [.rip] := rfl

/-- A NOP writes no memory. -/
theorem nopEffect_avoids (p : BitVec 64) (len : Nat) (code : CodeMap) :
    (nopEffect p len).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

/-- The effect of a NOP step: `afterStep` with `withNextIP` to `p + len` holds `nopEffect`. -/
theorem nopEffect_holds [Bindings] {s : RamState} (h : ReadyToStep s) (len : Nat) :
    (nopEffect s.RIP len).Holds s
      (afterStep s len fun t => withNextIP t (BitVec.add s.RIP (BitVec.ofNat 64 len))) :=
  ⟨afterStep_withNextIP_rip h len _, trivial, trivial, AgreesExcept.afterStep_withNextIP s len _⟩

/-- The step behind `nop_triple`: from a ready state with the instruction in memory and the
precondition, one `step` reaches a ready state with the effect `nopEffect`. -/
theorem nop_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x90]) (fun _ => nopEffect p 1) := by
  rintro s h hcode rfl
  exact ⟨_, nop_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_withNextIP h 1 _, nopEffect_holds h 1⟩

/-- The triple for `nop` (`90`) at `p`: only RIP moves, to `p + 1`. -/
theorem nop_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => s.RIP = p) (codeRange p [0x90]) (Effect.post fun _ => nopEffect p 1) :=
  Triple.of_effect (fun _ _ => nopEffect_avoids p 1 _)
    (nop_effect_step p)

/-- The step behind `nop_66_triple`: from a ready state with the instruction in memory and the
precondition, one `step` reaches a ready state with the effect `nopEffect`. -/
theorem nop_66_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0x90])
      (fun _ => nopEffect p 2) := by
  rintro s h hcode rfl
  exact ⟨_, nop_66_step s h hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_withNextIP h 2 _, nopEffect_holds h 2⟩

/-- The triple for `66 90` (`xchg ax, ax`) at `p`: only RIP moves, to `p + 2`. -/
theorem nop_66_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, 0x90])
      (Effect.post fun _ => nopEffect p 2) :=
  Triple.of_effect (fun _ _ => nopEffect_avoids p 2 _)
    (nop_66_effect_step p)

/-- The step behind `nop_r_triple`: from a ready state with the instruction in memory and the
precondition, one `step` reaches a ready state with the effect `nopEffect`. -/
theorem nop_r_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x0F, 0x1F, modrm])
      (fun _ => nopEffect p 3) := by
  rintro s h hcode rfl
  exact ⟨_, nop_r_step s h modrm hmod hreg hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_withNextIP h 3 _, nopEffect_holds h 3⟩

/-- The triple for `nop r/m32` with a register operand (`0F 1F /0`, `mod = 3`) at `p`: only RIP
moves, to `p + 3`. -/
theorem nop_r_triple [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) :
    Triple (fun s => s.RIP = p) (codeRange p [0x0F, 0x1F, modrm])
      (Effect.post fun _ => nopEffect p 3) :=
  Triple.of_effect (fun _ _ => nopEffect_avoids p 3 _)
    (nop_r_effect_step p modrm hmod hreg)
attribute [x86_compose] nopEffect

@[x86_local] theorem nopEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (fun _ => nopEffect p len) := by
  effect_local [nopEffect]

end X86Proofs
