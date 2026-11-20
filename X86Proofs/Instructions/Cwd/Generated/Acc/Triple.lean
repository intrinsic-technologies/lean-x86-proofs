import X86Proofs.Instructions.Cwd.Generated.Acc.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cqoEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 2 : Operand 64),
      cwdSpec ((Operand.reg 0 : Operand 64).read s)⟩] }

@[simp] theorem cqoEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (cqoEffect p len s).components = [.reg 2, .rip] := rfl

def cdqEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 2 : Operand 64),
      (cwdSpec ((Operand.reg 0 : Operand 32).read s)).setWidth 64⟩] }

@[simp] theorem cdqEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (cdqEffect p len s).components = [.reg 2, .rip] := rfl

def cwdEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 2 : Operand 64),
      mergeGPR 16 (cwdSpec ((Operand.reg 0 : Operand 16).read s))
        ((Operand.reg 2 : Operand 64).read s)⟩] }

@[simp] theorem cwdEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (cwdEffect p len s).components = [.reg 2, .rip] := rfl

theorem cqo_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x99]) (cqoEffect p 2) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cqo_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.rex_w s.DS)
    hcode.bytesAt hlow
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self]

theorem cqo_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0x99])
      (Effect.post (cqoEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cqoEffect_components]; simp [Component.Covers]) _)
    (cqo_effect_step p rex hrex)

theorem cqo_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => s.RIP = p) (codeRange p [0x48, 0x99])
      (Effect.post (cqoEffect p 2)) :=
  cqo_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide)

theorem cdq_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x99]) (cdqEffect p 1) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cdq_step s h [] (by simp) (by simp)
    (by rfl) (by rfl)
    (by rfl)
    (by rfl)
    hcode.bytesAt hlow
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32]

theorem cdq_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => s.RIP = p) (codeRange p [0x99])
      (Effect.post (cdqEffect p 1)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cdqEffect_components]; simp [Component.Covers]) _)
    (cdq_effect_step p)

theorem cwd_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0x99]) (cwdEffect p 2) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cwd_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    (by rfl) (by rfl)
    (by rfl)
    (by rfl)
    hcode.bytesAt hlow
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch]

theorem cwd_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, 0x99])
      (Effect.post (cwdEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cwdEffect_components]; simp [Component.Covers]) _)
    (cwd_effect_step p)

attribute [x86_compose] cqoEffect cdqEffect cwdEffect

@[x86_local] theorem cqoEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (cqoEffect p len) := by
  effect_local [cqoEffect]

@[x86_local] theorem cdqEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (cdqEffect p len) := by
  effect_local [cdqEffect]

@[x86_local] theorem cwdEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (cwdEffect p len) := by
  effect_local [cwdEffect]

end X86Proofs
