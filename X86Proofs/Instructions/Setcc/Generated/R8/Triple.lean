import X86Proofs.Instructions.Setcc.Generated.R8.Step
import X86Proofs.Instructions.Setcc.Generated.R8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def setccR8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Bool) (s : RamState) :
    Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 (if c then 1 else 0) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := none }

@[simp] theorem setccR8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Bool)
    (s : RamState) : (setccR8Effect p len dst c s).components = [.reg dst, .rip] := rfl

theorem setcc_r8_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hrm8 : (modrmRm modrm).toNat < 4)
    (c : Bool) :
    StepEffect (fun s => s.RIP = p ∧ condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p ([0x0F, setccOpcode cc, modrm]))
      (setccR8Effect p 3 (gprNumber 0 0 (modrmRm modrm)) c) := by
  rintro s h hcode ⟨hp, hc⟩
  subst hp hc
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := setcc_r8_step s h [] (by simp) (by simp)
    (by rfl) (by rfl) cc modrm hmod
    (.inr (gprNumber_zero_lt_four hrm8))
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, setccSpec]

theorem setcc_r8_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hrm8 : (modrmRm modrm).toNat < 4)
    (c : Bool) :
    Triple (fun s => s.RIP = p ∧ condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p ([0x0F, setccOpcode cc, modrm]))
      (Effect.post (setccR8Effect p 3 (gprNumber 0 0 (modrmRm modrm)) c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [setccR8Effect_components]; simp [Component.Covers]) _)
    (setcc_r8_effect_step p cc modrm hmod hrm8 c)

theorem setcc_r8_rex_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3)
    (c : Bool) :
    StepEffect (fun s => s.RIP = p ∧ condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p ([rex, 0x0F, setccOpcode cc, modrm]))
      (setccR8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) c) := by
  rintro s h hcode ⟨hp, hc⟩
  subst hp hc
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := setcc_r8_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) cc modrm hmod
    (.inl (by rw [scanContext_rex _ _ hr]; rfl))
    hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, setccSpec]

theorem setcc_r8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3)
    (c : Bool) :
    Triple (fun s => s.RIP = p ∧ condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p ([rex, 0x0F, setccOpcode cc, modrm]))
      (Effect.post (setccR8Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [setccR8Effect_components]; simp [Component.Covers]) _)
    (setcc_r8_rex_effect_step p cc rex hr modrm hmod c)

theorem setcc_r8_triple [Bindings] (p : BitVec 64) (cc : BitVec 4) (dst : BitVec 4) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (encodeSetccR8 cc dst))
      (Effect.post (setccR8Effect p (encodeSetccR8 cc dst).length (dst.setWidth 5) c)) := by
  rcases encodeSetccR8_spec cc dst with ⟨modrm, hbytes, hmod, hrm8, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst⟩
  · rw [hbytes, ← hdst]
    exact setcc_r8_triple_of_bytes p cc modrm hmod hrm8 c
  · rw [hbytes, ← hdst]
    exact setcc_r8_rex_triple_of_bytes p cc rex hrex modrm hmod c

def setccR8NoRexEffect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (c : Bool) (s : RamState) :
    Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg (byteRegGpr dst) : Operand 64),
      mergeByteReg dst (if c then 1 else 0) ((Operand.reg (byteRegGpr dst) : Operand 64).read s)⟩]
    flags := none }

@[simp] theorem setccR8NoRexEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (c : Bool) (s : RamState) :
    (setccR8NoRexEffect p len dst c s).components = [.reg (byteRegGpr dst), .rip] := rfl

theorem setcc_r8_norex_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    StepEffect (fun s => s.RIP = p ∧ condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p ([0x0F, setccOpcode cc, modrm]))
      (setccR8NoRexEffect p 3 (modrmRm modrm) c) := by
  rintro s h hcode ⟨hp, hc⟩
  subst hp hc
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := setcc_r8_gpr8_step s h [] (by simp) (by simp)
    (by rfl) (by rfl) cc modrm hmod hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : Operand.gpr8 (gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (modrmRm modrm))
      (byteRex (scanContext s.DS (PrefixSegments.ofState s) [])) = Operand.byteReg (modrmRm modrm) := rfl
  rw [hdst] at hstep
  simp only [writeResult_byteReg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, Operand.read_afterFetches,
    Operand.read_beforeFetch, setccSpec]

theorem setcc_r8_norex_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p ([0x0F, setccOpcode cc, modrm]))
      (Effect.post (setccR8NoRexEffect p 3 (modrmRm modrm) c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [setccR8NoRexEffect_components]; simp [Component.Covers]) _)
    (setcc_r8_norex_effect_step p cc modrm hmod c)

theorem setcc_r8_norex_triple [Bindings] (p : BitVec 64) (cc : BitVec 4) (dst : BitVec 3)
    (c : Bool) :
    Triple (fun s => s.RIP = p ∧ condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (encodeSetccR8NoRex cc dst))
      (Effect.post (setccR8NoRexEffect p 3 dst c)) := by
  have h := setcc_r8_norex_triple_of_bytes p cc (modrmRegs 0 dst) (modrmMod_modrmRegs _ _) c
  rwa [modrmRm_modrmRegs] at h

attribute [x86_compose] setccR8Effect setccR8NoRexEffect

@[x86_local] theorem setccR8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {c : Bool} :
    Effect.Local (setccR8Effect p len dst c) := by
  effect_local [setccR8Effect]

@[x86_local] theorem setccR8NoRexEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {c : Bool} : Effect.Local (setccR8NoRexEffect p len dst c) := by
  effect_local [setccR8NoRexEffect]

end X86Proofs
