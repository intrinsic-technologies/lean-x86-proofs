import X86Proofs.Instructions.Imul.Generated.M.Step
import X86Proofs.Instructions.Imul.Generated.M.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def imulM64Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Effect :=
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  let a := (Operand.reg 0 : Operand 64).read s
  let r := imulWideResult a b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64), r.1⟩,
      ⟨(Operand.reg 2 : Operand 64), r.2⟩]
    flags := some (imulWideFlags a b) }

@[simp] theorem imulM64Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) :
    (imulM64Effect p len am s).components = [.reg 0, .reg 2, .flags, .rip] := rfl

def imulM32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Effect :=
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 32).read s
  let a := (Operand.reg 0 : Operand 32).read s
  let r := imulWideResult a b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64), r.1.setWidth 64⟩,
      ⟨(Operand.reg 2 : Operand 64), r.2.setWidth 64⟩]
    flags := some (imulWideFlags a b) }

@[simp] theorem imulM32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) :
    (imulM32Effect p len am s).components = [.reg 0, .reg 2, .flags, .rip] := rfl

def imulM16Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Effect :=
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  let a := (Operand.reg 0 : Operand 16).read s
  let r := imulWideResult a b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64), mergeGPR 16 r.1 ((Operand.reg 0 : Operand 64).read s)⟩,
      ⟨(Operand.reg 2 : Operand 64), mergeGPR 16 r.2 ((Operand.reg 2 : Operand 64).read s)⟩]
    flags := some (imulWideFlags a b) }

@[simp] theorem imulM16Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) :
    (imulM16Effect p len am s).components = [.reg 0, .reg 2, .flags, .rip] := rfl

def imulM64SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode) (s : RamState) :
    Effect :=
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  let a := (Operand.reg 0 : Operand 64).read s
  let r := imulWideResult a b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64), r.1⟩,
      ⟨(Operand.reg 2 : Operand 64), r.2⟩]
    flags := some (imulWideFlags a b) }

@[simp] theorem imulM64SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (am : AddrMode) (s : RamState) : (imulM64SegEffect p len base am s).components = [.reg 0, .reg 2, .flags, .rip] := rfl

def imulM32SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode) (s : RamState) :
    Effect :=
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 32).read s
  let a := (Operand.reg 0 : Operand 32).read s
  let r := imulWideResult a b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64), r.1.setWidth 64⟩,
      ⟨(Operand.reg 2 : Operand 64), r.2.setWidth 64⟩]
    flags := some (imulWideFlags a b) }

@[simp] theorem imulM32SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (am : AddrMode) (s : RamState) : (imulM32SegEffect p len base am s).components = [.reg 0, .reg 2, .flags, .rip] := rfl

def imulM16SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode) (s : RamState) :
    Effect :=
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  let a := (Operand.reg 0 : Operand 16).read s
  let r := imulWideResult a b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64), mergeGPR 16 r.1 ((Operand.reg 0 : Operand 64).read s)⟩,
      ⟨(Operand.reg 2 : Operand 64), mergeGPR 16 r.2 ((Operand.reg 2 : Operand 64).read s)⟩]
    flags := some (imulWideFlags a b) }

@[simp] theorem imulM16SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (am : AddrMode) (s : RamState) : (imulM16SegEffect p len base am s).components = [.reg 0, .reg 2, .flags, .rip] := rfl

def imulM64A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Effect :=
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  let a := (Operand.reg 0 : Operand 64).read s
  let r := imulWideResult a b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64), r.1⟩,
      ⟨(Operand.reg 2 : Operand 64), r.2⟩]
    flags := some (imulWideFlags a b) }

@[simp] theorem imulM64A32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (s : RamState) : (imulM64A32Effect p len am s).components = [.reg 0, .reg 2, .flags, .rip] := rfl

def imulM32A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Effect :=
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 32).read s
  let a := (Operand.reg 0 : Operand 32).read s
  let r := imulWideResult a b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64), r.1.setWidth 64⟩,
      ⟨(Operand.reg 2 : Operand 64), r.2.setWidth 64⟩]
    flags := some (imulWideFlags a b) }

@[simp] theorem imulM32A32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (s : RamState) : (imulM32A32Effect p len am s).components = [.reg 0, .reg 2, .flags, .rip] := rfl

def imulM16A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Effect :=
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  let a := (Operand.reg 0 : Operand 16).read s
  let r := imulWideResult a b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64), mergeGPR 16 r.1 ((Operand.reg 0 : Operand 64).read s)⟩,
      ⟨(Operand.reg 2 : Operand 64), mergeGPR 16 r.2 ((Operand.reg 2 : Operand 64).read s)⟩]
    flags := some (imulWideFlags a b) }

@[simp] theorem imulM16A32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (s : RamState) : (imulM16A32Effect p len am s).components = [.reg 0, .reg 2, .flags, .rip] := rfl

theorem imul_m64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 8)
      (codeRange p (rex :: 0xF7 :: am.modrm 5 :: am.tail))
      (imulM64Effect p (3 + am.tail.length) am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := imul_m_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 4 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 4 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [imulWideSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch, mergeGPR_64]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulWideFlags_allows _ _ _

theorem imul_m64_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 8)
      (codeRange p (rex :: 0xF7 :: am.modrm 5 :: am.tail))
      (Effect.post (imulM64Effect p (3 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulM64Effect_components]; simp [Component.Covers]) _)
    (imul_m64_effect_step p rex hrex am hv hx hb)

theorem imul_m32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 4)
      (codeRange p (0xF7 :: am.modrm 5 :: am.tail))
      (imulM32Effect p (2 + am.tail.length) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := imul_m_step s h [] (by simp) (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 4 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 4 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [imulWideSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch, mergeGPR_32]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulWideFlags_allows _ _ _

theorem imul_m32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 4)
      (codeRange p (0xF7 :: am.modrm 5 :: am.tail))
      (Effect.post (imulM32Effect p (2 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulM32Effect_components]; simp [Component.Covers]) _)
    (imul_m32_effect_step p am hv hx hb)

theorem imul_m32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (rex :: 0xF7 :: am.modrm 5 :: am.tail))
      (imulM32Effect p (3 + am.tail.length) am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := imul_m_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 4 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 4 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [imulWideSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch, mergeGPR_32]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulWideFlags_allows _ _ _

theorem imul_m32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (rex :: 0xF7 :: am.modrm 5 :: am.tail))
      (Effect.post (imulM32Effect p (3 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulM32Effect_components]; simp [Component.Covers]) _)
    (imul_m32_rex_effect_step p rex hrex am hv hx hb)

theorem imul_m16_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 2)
      (codeRange p (0x66 :: 0xF7 :: am.modrm 5 :: am.tail))
      (imulM16Effect p (3 + am.tail.length) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := imul_m16_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) am hv
    (by exact (AddrContext.osz _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 4 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 4 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [imulWideSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulWideFlags_allows _ _ _

theorem imul_m16_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 2)
      (codeRange p (0x66 :: 0xF7 :: am.modrm 5 :: am.tail))
      (Effect.post (imulM16Effect p (3 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulM16Effect_components]; simp [Component.Covers]) _)
    (imul_m16_effect_step p am hv hx hb)

theorem imul_m16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (0x66 :: rex :: 0xF7 :: am.modrm 5 :: am.tail))
      (imulM16Effect p (4 + am.tail.length) am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := imul_m16_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_66_rex _ _ hr]; exact (AddrContext.oszRex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_66_rex _ _ hr]; exact hread)
  simp only [scanContext_66_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 4 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 4 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [imulWideSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulWideFlags_allows _ _ _

theorem imul_m16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (0x66 :: rex :: 0xF7 :: am.modrm 5 :: am.tail))
      (Effect.post (imulM16Effect p (4 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulM16Effect_components]; simp [Component.Covers]) _)
    (imul_m16_rex_effect_step p rex hrex am hv hx hb)

theorem imul_m64_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (r.prefixByte :: rex :: 0xF7 :: am.modrm 5 :: am.tail))
      (imulM64SegEffect p (4 + am.tail.length) base am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := imul_m_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 4 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 4 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [imulWideSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch, mergeGPR_64]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulWideFlags_allows _ _ _

theorem imul_m64_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (r.prefixByte :: rex :: 0xF7 :: am.modrm 5 :: am.tail))
      (Effect.post (imulM64SegEffect p (4 + am.tail.length) base am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulM64SegEffect_components]; simp [Component.Covers]) _)
    (imul_m64_seg_effect_step p r base rex hrex am hv hx hb)

theorem imul_m32_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: 0xF7 :: am.modrm 5 :: am.tail))
      (imulM32SegEffect p (3 + am.tail.length) base am) := by
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := imul_m_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 4 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 4 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [imulWideSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch, mergeGPR_32]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulWideFlags_allows _ _ _

theorem imul_m32_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: 0xF7 :: am.modrm 5 :: am.tail))
      (Effect.post (imulM32SegEffect p (3 + am.tail.length) base am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulM32SegEffect_components]; simp [Component.Covers]) _)
    (imul_m32_seg_effect_step p r base am hv hx hb)

theorem imul_m32_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: rex :: 0xF7 :: am.modrm 5 :: am.tail))
      (imulM32SegEffect p (4 + am.tail.length) base am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := imul_m_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 4 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 4 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [imulWideSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch, mergeGPR_32]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulWideFlags_allows _ _ _

theorem imul_m32_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: rex :: 0xF7 :: am.modrm 5 :: am.tail))
      (Effect.post (imulM32SegEffect p (4 + am.tail.length) base am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulM32SegEffect_components]; simp [Component.Covers]) _)
    (imul_m32_rex_seg_effect_step p r base rex hrex am hv hx hb)

theorem imul_m16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: 0xF7 :: am.modrm 5 :: am.tail))
      (imulM16SegEffect p (4 + am.tail.length) base am) := by
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66]
      (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil)]
  have hstep := imul_m16_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 4 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 4 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [imulWideSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulWideFlags_allows _ _ _

theorem imul_m16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: 0xF7 :: am.modrm 5 :: am.tail))
      (Effect.post (imulM16SegEffect p (4 + am.tail.length) base am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulM16SegEffect_components]; simp [Component.Covers]) _)
    (imul_m16_seg_effect_step p r base am hv hx hb)

theorem imul_m16_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0xF7 :: am.modrm 5 :: am.tail))
      (imulM16SegEffect p (5 + am.tail.length) base am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66, rex] =
      withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66, rex]
      (noSegPrefix_cons noSegPrefix_66 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_66_rex _ _ hr]
  have hstep := imul_m16_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 4 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 4 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [imulWideSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulWideFlags_allows _ _ _

theorem imul_m16_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0xF7 :: am.modrm 5 :: am.tail))
      (Effect.post (imulM16SegEffect p (5 + am.tail.length) base am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulM16SegEffect_components]; simp [Component.Covers]) _)
    (imul_m16_rex_seg_effect_step p r base rex hrex am hv hx hb)

theorem imul_m64_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (0x67 :: rex :: 0xF7 :: am.modrm 5 :: am.tail))
      (imulM64A32Effect p (4 + am.tail.length) am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := imul_m_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 4 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 4 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [imulWideSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch, mergeGPR_64]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulWideFlags_allows _ _ _

theorem imul_m64_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (0x67 :: rex :: 0xF7 :: am.modrm 5 :: am.tail))
      (Effect.post (imulM64A32Effect p (4 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulM64A32Effect_components]; simp [Component.Covers]) _)
    (imul_m64_a32_effect_step p rex hrex am hv hx hb)

theorem imul_m32_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (0x67 :: 0xF7 :: am.modrm 5 :: am.tail))
      (imulM32A32Effect p (3 + am.tail.length) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := imul_m_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 4 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 4 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [imulWideSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch, mergeGPR_32]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulWideFlags_allows _ _ _

theorem imul_m32_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (0x67 :: 0xF7 :: am.modrm 5 :: am.tail))
      (Effect.post (imulM32A32Effect p (3 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulM32A32Effect_components]; simp [Component.Covers]) _)
    (imul_m32_a32_effect_step p am hv hx hb)

theorem imul_m32_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (0x67 :: rex :: 0xF7 :: am.modrm 5 :: am.tail))
      (imulM32A32Effect p (4 + am.tail.length) am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := imul_m_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 4 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 4 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [imulWideSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch, mergeGPR_32]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulWideFlags_allows _ _ _

theorem imul_m32_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (0x67 :: rex :: 0xF7 :: am.modrm 5 :: am.tail))
      (Effect.post (imulM32A32Effect p (4 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulM32A32Effect_components]; simp [Component.Covers]) _)
    (imul_m32_rex_a32_effect_step p rex hrex am hv hx hb)

theorem imul_m16_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: 0xF7 :: am.modrm 5 :: am.tail))
      (imulM16A32Effect p (4 + am.tail.length) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66]) := by
    rw [scanContext_asz_cons]
  have hstep := imul_m16_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 4 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 4 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [imulWideSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulWideFlags_allows _ _ _

theorem imul_m16_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: 0xF7 :: am.modrm 5 :: am.tail))
      (Effect.post (imulM16A32Effect p (4 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulM16A32Effect_components]; simp [Component.Covers]) _)
    (imul_m16_a32_effect_step p am hv hx hb)

theorem imul_m16_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: rex :: 0xF7 :: am.modrm 5 :: am.tail))
      (imulM16A32Effect p (5 + am.tail.length) am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66, rex] =
      withAsz (oszRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_66_rex _ _ hr]
  have hstep := imul_m16_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 4 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 4 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 4 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [imulWideSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulWideFlags_allows _ _ _

theorem imul_m16_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: rex :: 0xF7 :: am.modrm 5 :: am.tail))
      (Effect.post (imulM16A32Effect p (5 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulM16A32Effect_components]; simp [Component.Covers]) _)
    (imul_m16_rex_a32_effect_step p rex hrex am hv hx hb)

theorem imul_m64_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 8)
      (codeRange p (encodeImulM64 am))
      (Effect.post (imulM64Effect p (3 + am.tail.length) am)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact imul_m64_triple_of_bytes p _ hrex am hv hx hb

theorem imul_m32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (encodeImulM32 am).length)) 4)
      (codeRange p (encodeImulM32 am))
      (Effect.post (imulM32Effect p (encodeImulM32 am).length am)) := by
  unfold encodeImulM32
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := imul_m32_triple_of_bytes p am hv hx hb
    rwa [show (0xF7 :: am.modrm 5 :: am.tail).length =
      2 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := imul_m32_rex_triple_of_bytes p _ hrex am hv hx hb
    rwa [show (am.rexByte false 0 :: 0xF7 :: am.modrm 5 :: am.tail).length =
      3 + am.tail.length by simp; omega]

theorem imul_m16_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (encodeImulM16 am).length)) 2)
      (codeRange p (encodeImulM16 am))
      (Effect.post (imulM16Effect p (encodeImulM16 am).length am)) := by
  unfold encodeImulM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := imul_m16_triple_of_bytes p am hv hx hb
    rwa [show (0x66 :: 0xF7 :: am.modrm 5 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := imul_m16_rex_triple_of_bytes p _ hrex am hv hx hb
    rwa [show (0x66 :: am.rexByte false 0 :: 0xF7 :: am.modrm 5 :: am.tail).length =
      4 + am.tail.length by simp; omega]

theorem imul_m64_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (r.prefixByte :: encodeImulM64 am))
      (Effect.post (imulM64SegEffect p (4 + am.tail.length) base am)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact imul_m64_seg_triple_of_bytes p r base _ hrex am hv hx hb

theorem imul_m32_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeImulM32 am).length)) 4)
      (codeRange p (r.prefixByte :: encodeImulM32 am))
      (Effect.post (imulM32SegEffect p (r.prefixByte :: encodeImulM32 am).length base
        am)) := by
  unfold encodeImulM32
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := imul_m32_seg_triple_of_bytes p r base am hv hx hb
    rwa [show (r.prefixByte :: 0xF7 :: am.modrm 5 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := imul_m32_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb
    rwa [show (r.prefixByte :: am.rexByte false 0 :: 0xF7 :: am.modrm 5 ::
      am.tail).length = 4 + am.tail.length by simp; omega]

theorem imul_m16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeImulM16 am).length)) 2)
      (codeRange p (r.prefixByte :: encodeImulM16 am))
      (Effect.post (imulM16SegEffect p (r.prefixByte :: encodeImulM16 am).length base
        am)) := by
  unfold encodeImulM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := imul_m16_seg_triple_of_bytes p r base am hv hx hb
    rwa [show (r.prefixByte :: 0x66 :: 0xF7 :: am.modrm 5 :: am.tail).length =
      4 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := imul_m16_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb
    rwa [show (r.prefixByte :: 0x66 :: am.rexByte false 0 :: 0xF7 :: am.modrm 5 ::
      am.tail).length = 5 + am.tail.length by simp; omega]

theorem imul_m64_a32_triple [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (0x67 :: encodeImulM64 am))
      (Effect.post (imulM64A32Effect p (4 + am.tail.length) am)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact imul_m64_a32_triple_of_bytes p _ hrex am hv hx hb

theorem imul_m32_a32_triple [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeImulM32 am).length)) 4)
      (codeRange p (0x67 :: encodeImulM32 am))
      (Effect.post (imulM32A32Effect p (0x67 :: encodeImulM32 am).length
        am)) := by
  unfold encodeImulM32
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := imul_m32_a32_triple_of_bytes p am hv hx hb
    rwa [show (0x67 :: 0xF7 :: am.modrm 5 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := imul_m32_rex_a32_triple_of_bytes p _ hrex am hv hx hb
    rwa [show (0x67 :: am.rexByte false 0 :: 0xF7 :: am.modrm 5 ::
      am.tail).length = 4 + am.tail.length by simp; omega]

theorem imul_m16_a32_triple [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeImulM16 am).length)) 2)
      (codeRange p (0x67 :: encodeImulM16 am))
      (Effect.post (imulM16A32Effect p (0x67 :: encodeImulM16 am).length
        am)) := by
  unfold encodeImulM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := imul_m16_a32_triple_of_bytes p am hv hx hb
    rwa [show (0x67 :: 0x66 :: 0xF7 :: am.modrm 5 :: am.tail).length =
      4 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := imul_m16_rex_a32_triple_of_bytes p _ hrex am hv hx hb
    rwa [show (0x67 :: 0x66 :: am.rexByte false 0 :: 0xF7 :: am.modrm 5 ::
      am.tail).length = 5 + am.tail.length by simp; omega]

attribute [x86_compose] imulM64Effect imulM32Effect imulM16Effect imulM64SegEffect imulM32SegEffect imulM16SegEffect imulM64A32Effect imulM32A32Effect imulM16A32Effect

@[x86_local] theorem imulM64Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (imulM64Effect p len am) := by
  effect_local [imulM64Effect, imulWideFlags]

@[x86_local] theorem imulM64SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} : Effect.Local (imulM64SegEffect p len base am) := by
  effect_local [imulM64SegEffect, imulWideFlags]

@[x86_local] theorem imulM64A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (imulM64A32Effect p len am) := by
  effect_local [imulM64A32Effect, imulWideFlags]

@[x86_local] theorem imulM32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (imulM32Effect p len am) := by
  effect_local [imulM32Effect, imulWideFlags]

@[x86_local] theorem imulM32SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} : Effect.Local (imulM32SegEffect p len base am) := by
  effect_local [imulM32SegEffect, imulWideFlags]

@[x86_local] theorem imulM32A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (imulM32A32Effect p len am) := by
  effect_local [imulM32A32Effect, imulWideFlags]

@[x86_local] theorem imulM16Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (imulM16Effect p len am) := by
  effect_local [imulM16Effect, imulWideFlags]

@[x86_local] theorem imulM16SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} : Effect.Local (imulM16SegEffect p len base am) := by
  effect_local [imulM16SegEffect, imulWideFlags]

@[x86_local] theorem imulM16A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (imulM16A32Effect p len am) := by
  effect_local [imulM16A32Effect, imulWideFlags]

end X86Proofs
