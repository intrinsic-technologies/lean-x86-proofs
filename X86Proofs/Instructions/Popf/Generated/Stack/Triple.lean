import X86Proofs.Instructions.Popf.Generated.Stack.Step
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Popf.OfHolds

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def popfqEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect :=
  let v := (Operand.mem (stackPtr s) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.df : Operand 1), dfBit v⟩, ⟨(Operand.reg 4 : Operand 64), stackPtr s + 8⟩]
    flags := some (.ofStatusFlags (StatusFlags.ofRFLAGS v)) }

@[simp] theorem popfqEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (popfqEffect p len s).components = [.df, .reg 4, .flags, .rip] := rfl

theorem popfq_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (PopfqPre p) (codeRange p [0x9D]) (popfqEffect p 1) := by
  rintro s h hcode hpre
  have hp := hpre.rip
  subst hp
  have hstep := popfq_step s h [] (by simp) (by simp) rfl rfl rfl
    hcode.bytesAt (hcode.low (by simp) (by simp)) hpre.read hpre.iopl
  refine ⟨_, hstep, ReadyToStep.afterStep_popfq h _ _ hpre.keeps,
    ⟨afterStep_popfq_rip h _ _, ⟨Operand.read_afterStep_popfq_df _ _ _,
      Operand.read_afterStep_popfq_rsp _ _ _⟩, ?_, AgreesExcept.afterStep_popfq _ _ _ hpre.keeps⟩⟩
  show StatusFlagsOutcome.Allows _ _
  rw [ofRFLAGS_afterStep_popfq]
  exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem popfq_triple [Bindings] (p : BitVec 64) :
    Triple (PopfqPre p) (codeRange p [0x9D]) (Effect.post (popfqEffect p 1)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [popfqEffect_components]; simp [Component.Covers]) _)
    (popfq_effect_step p)

attribute [x86_compose] popfqEffect

@[x86_local] theorem popfqEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (popfqEffect p len) := by
  effect_local [popfqEffect, stackPtr]

def popfEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect :=
  let v := ((Operand.mem (stackPtr s) : Operand 16).read s).setWidth 64
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.df : Operand 1), dfBit v⟩, ⟨(Operand.reg 4 : Operand 64), stackPtr s + 2⟩]
    flags := some (.ofStatusFlags (StatusFlags.ofRFLAGS v)) }

@[simp] theorem popfEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (popfEffect p len s).components = [.df, .reg 4, .flags, .rip] := rfl

theorem popf_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (PopfPre p) (codeRange p [0x66, 0x9D]) (popfEffect p 2) := by
  rintro s h hcode hpre
  have hp := hpre.rip
  subst hp
  have hstep := popf_step s h [0x66] (by simpa using scanPrefix_66) (by simp) rfl rfl rfl rfl
    hcode.bytesAt (hcode.low (by simp) (by simp)) hpre.read hpre.iopl
  refine ⟨_, hstep, ReadyToStep.afterStep_popf h _ _ hpre.keeps,
    ⟨afterStep_popf_rip h _ _, ⟨Operand.read_afterStep_popf_df _ _ _,
      Operand.read_afterStep_popf_rsp _ _ _⟩, ?_, AgreesExcept.afterStep_popf _ _ _ hpre.keeps⟩⟩
  show StatusFlagsOutcome.Allows _ _
  rw [ofRFLAGS_afterStep_popf]
  exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem popf_triple [Bindings] (p : BitVec 64) :
    Triple (PopfPre p) (codeRange p [0x66, 0x9D]) (Effect.post (popfEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [popfEffect_components]; simp [Component.Covers]) _)
    (popf_effect_step p)

attribute [x86_compose] popfEffect

@[x86_local] theorem popfEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (popfEffect p len) := by
  effect_local [popfEffect, stackPtr]

end X86Proofs
