import X86Proofs.Instructions.Cbw.Generated.Acc.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cdqeEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64),
      cbwSpec 64 ((Operand.reg 0 : Operand 32).read s)⟩] }

@[simp] theorem cdqeEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (cdqeEffect p len s).components = [.reg 0, .rip] := rfl

def cwdeEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64),
      (cbwSpec 32 ((Operand.reg 0 : Operand 16).read s)).setWidth 64⟩] }

@[simp] theorem cwdeEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (cwdeEffect p len s).components = [.reg 0, .rip] := rfl

def cbwEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 16 (cbwSpec 16 ((Operand.reg 0 : Operand 8).read s))
        ((Operand.reg 0 : Operand 64).read s)⟩] }

@[simp] theorem cbwEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (cbwEffect p len s).components = [.reg 0, .rip] := rfl

theorem cdqe_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x98]) (cdqeEffect p 2) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cdqe_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.rex_w s.DS)
    hcode.bytesAt hlow
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self]

theorem cdqe_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0x98])
      (Effect.post (cdqeEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cdqeEffect_components]; simp [Component.Covers]) _)
    (cdqe_effect_step p rex hrex)

theorem cdqe_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => s.RIP = p) (codeRange p [0x48, 0x98])
      (Effect.post (cdqeEffect p 2)) :=
  cdqe_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide)

theorem cwde_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x98]) (cwdeEffect p 1) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cwde_step s h [] (by simp) (by simp)
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

theorem cwde_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => s.RIP = p) (codeRange p [0x98])
      (Effect.post (cwdeEffect p 1)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cwdeEffect_components]; simp [Component.Covers]) _)
    (cwde_effect_step p)

theorem cbw_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, 0x98]) (cbwEffect p 2) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cbw_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
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

theorem cbw_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, 0x98])
      (Effect.post (cbwEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cbwEffect_components]; simp [Component.Covers]) _)
    (cbw_effect_step p)

attribute [x86_compose] cdqeEffect cwdeEffect cbwEffect

@[x86_local] theorem cdqeEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (cdqeEffect p len) := by
  effect_local [cdqeEffect]

@[x86_local] theorem cwdeEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (cwdeEffect p len) := by
  effect_local [cwdeEffect]

@[x86_local] theorem cbwEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (cbwEffect p len) := by
  effect_local [cbwEffect]

end X86Proofs
