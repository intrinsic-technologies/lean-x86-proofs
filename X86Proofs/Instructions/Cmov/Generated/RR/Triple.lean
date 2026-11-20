import X86Proofs.Instructions.Cmov.Generated.RR.Step
import X86Proofs.Instructions.Cmov.Generated.RR.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cmovR64R64Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (c : Bool) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := (Operand.reg src : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), if c then b else a⟩]
    flags := none }

@[simp] theorem cmovR64R64Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (c : Bool) (s : RamState) :
    (cmovR64R64Effect p len dst src c s).components = [.reg dst, .rip] := rfl

def cmovR32R32Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (c : Bool) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  let b := (Operand.reg src : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (if c then b else a).setWidth 64⟩]
    flags := none }

@[simp] theorem cmovR32R32Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (c : Bool) (s : RamState) :
    (cmovR32R32Effect p len dst src c s).components = [.reg dst, .rip] := rfl

def cmovR16R16Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (c : Bool) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  let b := (Operand.reg src : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (if c then b else a) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := none }

@[simp] theorem cmovR16R16Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (c : Bool) (s : RamState) :
    (cmovR16R16Effect p len dst src c s).components = [.reg dst, .rip] := rfl

theorem cmov_r64_r64_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    StepEffect (fun s => s.RIP = p ∧ condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p ([rex, 0x0F, cmovOpcode cc, modrm]))
      (cmovR64R64Effect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) c) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hc⟩
  subst hp hc
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cmov_r_r_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) cc modrm hmod
    hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, cmovSpec]

theorem cmov_r64_r64_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p ([rex, 0x0F, cmovOpcode cc, modrm]))
      (Effect.post
        (cmovR64R64Effect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmovR64R64Effect_components]; simp [Component.Covers]) _)
    (cmov_r64_r64_effect_step p cc rex hrex modrm hmod c)

theorem cmov_r32_r32_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    StepEffect (fun s => s.RIP = p ∧ condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p ([0x0F, cmovOpcode cc, modrm]))
      (cmovR32R32Effect p 3 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) c) := by
  rintro s h hcode ⟨hp, hc⟩
  subst hp hc
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cmov_r_r_step s h [] (by simp) (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl) cc modrm hmod
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, cmovSpec]

theorem cmov_r32_r32_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p ([0x0F, cmovOpcode cc, modrm]))
      (Effect.post
        (cmovR32R32Effect p 3 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmovR32R32Effect_components]; simp [Component.Covers]) _)
    (cmov_r32_r32_effect_step p cc modrm hmod c)

theorem cmov_r32_r32_rex_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    StepEffect (fun s => s.RIP = p ∧ condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p ([rex, 0x0F, cmovOpcode cc, modrm]))
      (cmovR32R32Effect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) c) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hc⟩
  subst hp hc
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cmov_r_r_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) cc modrm hmod
    hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, cmovSpec]

theorem cmov_r32_r32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p ([rex, 0x0F, cmovOpcode cc, modrm]))
      (Effect.post
        (cmovR32R32Effect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmovR32R32Effect_components]; simp [Component.Covers]) _)
    (cmov_r32_r32_rex_effect_step p cc rex hrex modrm hmod c)

theorem cmov_r16_r16_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    StepEffect (fun s => s.RIP = p ∧ condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p ([0x66, 0x0F, cmovOpcode cc, modrm]))
      (cmovR16R16Effect p 4 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) c) := by
  rintro s h hcode ⟨hp, hc⟩
  subst hp hc
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cmov_r16_r16_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    (by exact rfl)
    (by rfl) (by rfl) cc modrm hmod
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, cmovSpec]

theorem cmov_r16_r16_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p ([0x66, 0x0F, cmovOpcode cc, modrm]))
      (Effect.post
        (cmovR16R16Effect p 4 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)) c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmovR16R16Effect_components]; simp [Component.Covers]) _)
    (cmov_r16_r16_effect_step p cc modrm hmod c)

theorem cmov_r16_r16_rex_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    StepEffect (fun s => s.RIP = p ∧ condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p ([0x66, rex, 0x0F, cmovOpcode cc, modrm]))
      (cmovR16R16Effect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) c) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hc⟩
  subst hp hc
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := cmov_r16_r16_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl) cc modrm hmod
    hcode.bytesAt hlow
  simp only [scanContext_66_rex _ _ hr] at hstep
  have hdst : gprNumber (oszRexContext s.DS rex.toBitVec).rex_r4
      (oszRexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  have hsrc : gprNumber (oszRexContext s.DS rex.toBitVec).rex_b4
      (oszRexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, cmovSpec]

theorem cmov_r16_r16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (c : Bool) :
    Triple (fun s => s.RIP = p ∧ condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p ([0x66, rex, 0x0F, cmovOpcode cc, modrm]))
      (Effect.post
        (cmovR16R16Effect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmovR16R16Effect_components]; simp [Component.Covers]) _)
    (cmov_r16_r16_rex_effect_step p cc rex hrex modrm hmod c)

theorem cmov_r64_r64_triple [Bindings] (p : BitVec 64) (cc : BitVec 4) (dst src : BitVec 4)
    (c : Bool) :
    Triple (fun s => s.RIP = p ∧ condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (encodeCmovR64R64 cc dst src))
      (Effect.post (cmovR64R64Effect p (encodeCmovR64R64 cc dst src).length (dst.setWidth 5)
        (src.setWidth 5) c)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeCmovR64R64_spec cc dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact cmov_r64_r64_triple_of_bytes p cc rex hrex modrm hmod c

theorem cmov_r32_r32_triple [Bindings] (p : BitVec 64) (cc : BitVec 4) (dst src : BitVec 4)
    (c : Bool) :
    Triple (fun s => s.RIP = p ∧ condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (encodeCmovR32R32 cc dst src))
      (Effect.post (cmovR32R32Effect p (encodeCmovR32R32 cc dst src).length (dst.setWidth 5)
        (src.setWidth 5) c)) := by
  rcases encodeCmovR32R32_spec cc dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact cmov_r32_r32_triple_of_bytes p cc modrm hmod c
  · rw [hbytes, ← hdst, ← hsrc]
    exact cmov_r32_r32_rex_triple_of_bytes p cc rex hrex modrm hmod c

theorem cmov_r16_r16_triple [Bindings] (p : BitVec 64) (cc : BitVec 4) (dst src : BitVec 4)
    (c : Bool) :
    Triple (fun s => s.RIP = p ∧ condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (encodeCmovR16R16 cc dst src))
      (Effect.post (cmovR16R16Effect p (encodeCmovR16R16 cc dst src).length (dst.setWidth 5)
        (src.setWidth 5) c)) := by
  rcases encodeCmovR16R16_spec cc dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact cmov_r16_r16_triple_of_bytes p cc modrm hmod c
  · rw [hbytes, ← hdst, ← hsrc]
    exact cmov_r16_r16_rex_triple_of_bytes p cc rex hrex modrm hmod c

attribute [x86_compose] cmovR64R64Effect cmovR32R32Effect cmovR16R16Effect

@[x86_local] theorem cmovR64R64Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 5} {c : Bool} :
    Effect.Local (cmovR64R64Effect p len dst src c) := by
  effect_local [cmovR64R64Effect]

@[x86_local] theorem cmovR32R32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 5} {c : Bool} :
    Effect.Local (cmovR32R32Effect p len dst src c) := by
  effect_local [cmovR32R32Effect]

@[x86_local] theorem cmovR16R16Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 5} {c : Bool} :
    Effect.Local (cmovR16R16Effect p len dst src c) := by
  effect_local [cmovR16R16Effect]

end X86Proofs
