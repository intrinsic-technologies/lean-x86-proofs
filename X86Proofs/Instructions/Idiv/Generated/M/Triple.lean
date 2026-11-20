import X86Proofs.Instructions.Idiv.Generated.M.Step
import X86Proofs.Instructions.Idiv.Generated.M.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def idivM64Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Effect :=
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  let t := (Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s
  let r := idivResult t b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 2 : Operand 64), r.2⟩,
      ⟨(Operand.reg 0 : Operand 64), r.1⟩]
    flags := some divFlags }

@[simp] theorem idivM64Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) :
    (idivM64Effect p len am s).components = [.reg 2, .reg 0, .flags, .rip] := rfl

def idivM32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Effect :=
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 32).read s
  let t := (Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s
  let r := idivResult t b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 2 : Operand 64), r.2.setWidth 64⟩,
      ⟨(Operand.reg 0 : Operand 64), r.1.setWidth 64⟩]
    flags := some divFlags }

@[simp] theorem idivM32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) :
    (idivM32Effect p len am s).components = [.reg 2, .reg 0, .flags, .rip] := rfl

def idivM16Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Effect :=
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  let t := (Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s
  let r := idivResult t b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 2 : Operand 64), mergeGPR 16 r.2 ((Operand.reg 2 : Operand 64).read s)⟩,
      ⟨(Operand.reg 0 : Operand 64), mergeGPR 16 r.1 ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some divFlags }

@[simp] theorem idivM16Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) :
    (idivM16Effect p len am s).components = [.reg 2, .reg 0, .flags, .rip] := rfl

def idivM64SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode) (s : RamState) :
    Effect :=
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  let t := (Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s
  let r := idivResult t b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 2 : Operand 64), r.2⟩,
      ⟨(Operand.reg 0 : Operand 64), r.1⟩]
    flags := some divFlags }

@[simp] theorem idivM64SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (am : AddrMode) (s : RamState) : (idivM64SegEffect p len base am s).components = [.reg 2, .reg 0, .flags, .rip] := rfl

def idivM32SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode) (s : RamState) :
    Effect :=
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 32).read s
  let t := (Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s
  let r := idivResult t b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 2 : Operand 64), r.2.setWidth 64⟩,
      ⟨(Operand.reg 0 : Operand 64), r.1.setWidth 64⟩]
    flags := some divFlags }

@[simp] theorem idivM32SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (am : AddrMode) (s : RamState) : (idivM32SegEffect p len base am s).components = [.reg 2, .reg 0, .flags, .rip] := rfl

def idivM16SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode) (s : RamState) :
    Effect :=
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  let t := (Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s
  let r := idivResult t b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 2 : Operand 64), mergeGPR 16 r.2 ((Operand.reg 2 : Operand 64).read s)⟩,
      ⟨(Operand.reg 0 : Operand 64), mergeGPR 16 r.1 ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some divFlags }

@[simp] theorem idivM16SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (am : AddrMode) (s : RamState) : (idivM16SegEffect p len base am s).components = [.reg 2, .reg 0, .flags, .rip] := rfl

def idivM64A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Effect :=
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  let t := (Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s
  let r := idivResult t b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 2 : Operand 64), r.2⟩,
      ⟨(Operand.reg 0 : Operand 64), r.1⟩]
    flags := some divFlags }

@[simp] theorem idivM64A32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (s : RamState) : (idivM64A32Effect p len am s).components = [.reg 2, .reg 0, .flags, .rip] := rfl

def idivM32A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Effect :=
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 32).read s
  let t := (Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s
  let r := idivResult t b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 2 : Operand 64), r.2.setWidth 64⟩,
      ⟨(Operand.reg 0 : Operand 64), r.1.setWidth 64⟩]
    flags := some divFlags }

@[simp] theorem idivM32A32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (s : RamState) : (idivM32A32Effect p len am s).components = [.reg 2, .reg 0, .flags, .rip] := rfl

def idivM16A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Effect :=
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  let t := (Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s
  let r := idivResult t b
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 2 : Operand 64), mergeGPR 16 r.2 ((Operand.reg 2 : Operand 64).read s)⟩,
      ⟨(Operand.reg 0 : Operand 64), mergeGPR 16 r.1 ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some divFlags }

@[simp] theorem idivM16A32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (s : RamState) : (idivM16A32Effect p len am s).components = [.reg 2, .reg 0, .flags, .rip] := rfl

theorem idiv_m64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (3 + am.tail.length))) 8 s ∧
      IdivDefined ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s)
            (
              (Operand.mem (am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand 64).read s))
      (codeRange p (rex :: 0xF7 :: am.modrm 7 :: am.tail))
      (idivM64Effect p (3 + am.tail.length) am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, hread⟩, hdef⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := idiv_m_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread) (by rw [scanContext_rex _ _ hr]; exact hdef)
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 6 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 6 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [idivSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch, mergeGPR_64]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact idiv_divFlags_allows _ _ _

theorem idiv_m64_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (3 + am.tail.length))) 8 s ∧
      IdivDefined ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s)
            (
              (Operand.mem (am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand 64).read s))
      (codeRange p (rex :: 0xF7 :: am.modrm 7 :: am.tail))
      (Effect.post (idivM64Effect p (3 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [idivM64Effect_components]; simp [Component.Covers]) _)
    (idiv_m64_effect_step p rex hrex am hv hx hb)

theorem idiv_m32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (2 + am.tail.length))) 4 s ∧
      IdivDefined ((Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s)
            (
              (Operand.mem (am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) : Operand 32).read s))
      (codeRange p (0xF7 :: am.modrm 7 :: am.tail))
      (idivM32Effect p (2 + am.tail.length) am) := by
  rintro s h hcode ⟨⟨hp, hread⟩, hdef⟩
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := idiv_m_step s h [] (by simp) (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread) (by exact hdef)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 6 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 6 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [idivSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch, mergeGPR_32]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact idiv_divFlags_allows _ _ _

theorem idiv_m32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (2 + am.tail.length))) 4 s ∧
      IdivDefined ((Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s)
            (
              (Operand.mem (am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) : Operand 32).read s))
      (codeRange p (0xF7 :: am.modrm 7 :: am.tail))
      (Effect.post (idivM32Effect p (2 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [idivM32Effect_components]; simp [Component.Covers]) _)
    (idiv_m32_effect_step p am hv hx hb)

theorem idiv_m32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (3 + am.tail.length))) 4 s ∧
      IdivDefined ((Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s)
            (
              (Operand.mem (am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand 32).read s))
      (codeRange p (rex :: 0xF7 :: am.modrm 7 :: am.tail))
      (idivM32Effect p (3 + am.tail.length) am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, hread⟩, hdef⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := idiv_m_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread) (by rw [scanContext_rex _ _ hr]; exact hdef)
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 6 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 6 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [idivSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch, mergeGPR_32]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact idiv_divFlags_allows _ _ _

theorem idiv_m32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (3 + am.tail.length))) 4 s ∧
      IdivDefined ((Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s)
            (
              (Operand.mem (am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand 32).read s))
      (codeRange p (rex :: 0xF7 :: am.modrm 7 :: am.tail))
      (Effect.post (idivM32Effect p (3 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [idivM32Effect_components]; simp [Component.Covers]) _)
    (idiv_m32_rex_effect_step p rex hrex am hv hx hb)

theorem idiv_m16_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧
      IdivDefined ((Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s)
            (
              (Operand.mem (am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand 16).read s))
      (codeRange p (0x66 :: 0xF7 :: am.modrm 7 :: am.tail))
      (idivM16Effect p (3 + am.tail.length) am) := by
  rintro s h hcode ⟨⟨hp, hread⟩, hdef⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := idiv_m16_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) am hv
    (by exact (AddrContext.osz _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread) (by exact hdef)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 6 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 6 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [idivSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact idiv_divFlags_allows _ _ _

theorem idiv_m16_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧
      IdivDefined ((Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s)
            (
              (Operand.mem (am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand 16).read s))
      (codeRange p (0x66 :: 0xF7 :: am.modrm 7 :: am.tail))
      (Effect.post (idivM16Effect p (3 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [idivM16Effect_components]; simp [Component.Covers]) _)
    (idiv_m16_effect_step p am hv hx hb)

theorem idiv_m16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
      IdivDefined ((Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s)
            (
              (Operand.mem (am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand 16).read s))
      (codeRange p (0x66 :: rex :: 0xF7 :: am.modrm 7 :: am.tail))
      (idivM16Effect p (4 + am.tail.length) am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, hread⟩, hdef⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := idiv_m16_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_66_rex _ _ hr]; exact (AddrContext.oszRex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_66_rex _ _ hr]; exact hread) (by rw [scanContext_66_rex _ _ hr]; exact hdef)
  simp only [scanContext_66_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 6 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 6 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [idivSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact idiv_divFlags_allows _ _ _

theorem idiv_m16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
      IdivDefined ((Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s)
            (
              (Operand.mem (am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand 16).read s))
      (codeRange p (0x66 :: rex :: 0xF7 :: am.modrm 7 :: am.tail))
      (Effect.post (idivM16Effect p (4 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [idivM16Effect_components]; simp [Component.Covers]) _)
    (idiv_m16_rex_effect_step p rex hrex am hv hx hb)

theorem idiv_m64_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => SegLoadPre p r base (fun u => am.addr u (p + BitVec.ofNat 64 (4 + am.tail.length))) 8 s ∧
      IdivDefined ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s)
            (
              (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand 64).read s))
      (codeRange p (r.prefixByte :: rex :: 0xF7 :: am.modrm 7 :: am.tail))
      (idivM64SegEffect p (4 + am.tail.length) base am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, ⟨hseg, hbase⟩, hread⟩, hdef⟩
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
  have hstep := idiv_m_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread) (by rw [hsc, segAddr_withSeg]; exact hdef)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 6 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 6 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [idivSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch, mergeGPR_64]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact idiv_divFlags_allows _ _ _

theorem idiv_m64_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => SegLoadPre p r base (fun u => am.addr u (p + BitVec.ofNat 64 (4 + am.tail.length))) 8 s ∧
      IdivDefined ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s)
            (
              (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand 64).read s))
      (codeRange p (r.prefixByte :: rex :: 0xF7 :: am.modrm 7 :: am.tail))
      (Effect.post (idivM64SegEffect p (4 + am.tail.length) base am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [idivM64SegEffect_components]; simp [Component.Covers]) _)
    (idiv_m64_seg_effect_step p r base rex hrex am hv hx hb)

theorem idiv_m32_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (fun s => SegLoadPre p r base (fun u => am.addr u (p + BitVec.ofNat 64 (3 + am.tail.length))) 4 s ∧
      IdivDefined ((Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s)
            (
              (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand 32).read s))
      (codeRange p (r.prefixByte :: 0xF7 :: am.modrm 7 :: am.tail))
      (idivM32SegEffect p (3 + am.tail.length) base am) := by
  rintro s h hcode ⟨⟨hp, ⟨hseg, hbase⟩, hread⟩, hdef⟩
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
  have hstep := idiv_m_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread) (by rw [hsc, segAddr_withSeg]; exact hdef)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 6 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 6 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [idivSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch, mergeGPR_32]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact idiv_divFlags_allows _ _ _

theorem idiv_m32_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (fun s => SegLoadPre p r base (fun u => am.addr u (p + BitVec.ofNat 64 (3 + am.tail.length))) 4 s ∧
      IdivDefined ((Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s)
            (
              (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand 32).read s))
      (codeRange p (r.prefixByte :: 0xF7 :: am.modrm 7 :: am.tail))
      (Effect.post (idivM32SegEffect p (3 + am.tail.length) base am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [idivM32SegEffect_components]; simp [Component.Covers]) _)
    (idiv_m32_seg_effect_step p r base am hv hx hb)

theorem idiv_m32_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => SegLoadPre p r base (fun u => am.addr u (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧
      IdivDefined ((Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s)
            (
              (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand 32).read s))
      (codeRange p (r.prefixByte :: rex :: 0xF7 :: am.modrm 7 :: am.tail))
      (idivM32SegEffect p (4 + am.tail.length) base am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, ⟨hseg, hbase⟩, hread⟩, hdef⟩
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
  have hstep := idiv_m_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread) (by rw [hsc, segAddr_withSeg]; exact hdef)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 6 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 6 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [idivSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch, mergeGPR_32]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact idiv_divFlags_allows _ _ _

theorem idiv_m32_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => SegLoadPre p r base (fun u => am.addr u (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧
      IdivDefined ((Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s)
            (
              (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand 32).read s))
      (codeRange p (r.prefixByte :: rex :: 0xF7 :: am.modrm 7 :: am.tail))
      (Effect.post (idivM32SegEffect p (4 + am.tail.length) base am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [idivM32SegEffect_components]; simp [Component.Covers]) _)
    (idiv_m32_rex_seg_effect_step p r base rex hrex am hv hx hb)

theorem idiv_m16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (fun s => SegLoadPre p r base (fun u => am.addr u (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
      IdivDefined ((Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s)
            (
              (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand 16).read s))
      (codeRange p (r.prefixByte :: 0x66 :: 0xF7 :: am.modrm 7 :: am.tail))
      (idivM16SegEffect p (4 + am.tail.length) base am) := by
  rintro s h hcode ⟨⟨hp, ⟨hseg, hbase⟩, hread⟩, hdef⟩
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
  have hstep := idiv_m16_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread) (by rw [hsc, segAddr_withSeg]; exact hdef)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 6 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 6 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [idivSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact idiv_divFlags_allows _ _ _

theorem idiv_m16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (fun s => SegLoadPre p r base (fun u => am.addr u (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
      IdivDefined ((Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s)
            (
              (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand 16).read s))
      (codeRange p (r.prefixByte :: 0x66 :: 0xF7 :: am.modrm 7 :: am.tail))
      (Effect.post (idivM16SegEffect p (4 + am.tail.length) base am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [idivM16SegEffect_components]; simp [Component.Covers]) _)
    (idiv_m16_seg_effect_step p r base am hv hx hb)

theorem idiv_m16_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => SegLoadPre p r base (fun u => am.addr u (p + BitVec.ofNat 64 (5 + am.tail.length))) 2 s ∧
      IdivDefined ((Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s)
            (
              (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) : Operand 16).read s))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0xF7 :: am.modrm 7 :: am.tail))
      (idivM16SegEffect p (5 + am.tail.length) base am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, ⟨hseg, hbase⟩, hread⟩, hdef⟩
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
  have hstep := idiv_m16_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread) (by rw [hsc, segAddr_withSeg]; exact hdef)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 6 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 6 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [idivSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact idiv_divFlags_allows _ _ _

theorem idiv_m16_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => SegLoadPre p r base (fun u => am.addr u (p + BitVec.ofNat 64 (5 + am.tail.length))) 2 s ∧
      IdivDefined ((Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s)
            (
              (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) : Operand 16).read s))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0xF7 :: am.modrm 7 :: am.tail))
      (Effect.post (idivM16SegEffect p (5 + am.tail.length) base am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [idivM16SegEffect_components]; simp [Component.Covers]) _)
    (idiv_m16_rex_seg_effect_step p r base rex hrex am hv hx hb)

theorem idiv_m64_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (4 + am.tail.length))) 8 s ∧
      IdivDefined ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s)
            (
              (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand 64).read s))
      (codeRange p (0x67 :: rex :: 0xF7 :: am.modrm 7 :: am.tail))
      (idivM64A32Effect p (4 + am.tail.length) am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, hread⟩, hdef⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := idiv_m_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread) (by rw [hsc]; exact hdef)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 6 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 6 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [idivSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch, mergeGPR_64]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact idiv_divFlags_allows _ _ _

theorem idiv_m64_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (4 + am.tail.length))) 8 s ∧
      IdivDefined ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s)
            (
              (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand 64).read s))
      (codeRange p (0x67 :: rex :: 0xF7 :: am.modrm 7 :: am.tail))
      (Effect.post (idivM64A32Effect p (4 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [idivM64A32Effect_components]; simp [Component.Covers]) _)
    (idiv_m64_a32_effect_step p rex hrex am hv hx hb)

theorem idiv_m32_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (3 + am.tail.length))) 4 s ∧
      IdivDefined ((Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s)
            (
              (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand 32).read s))
      (codeRange p (0x67 :: 0xF7 :: am.modrm 7 :: am.tail))
      (idivM32A32Effect p (3 + am.tail.length) am) := by
  rintro s h hcode ⟨⟨hp, hread⟩, hdef⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := idiv_m_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread) (by rw [hsc]; exact hdef)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 6 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 6 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [idivSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch, mergeGPR_32]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact idiv_divFlags_allows _ _ _

theorem idiv_m32_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (3 + am.tail.length))) 4 s ∧
      IdivDefined ((Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s)
            (
              (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand 32).read s))
      (codeRange p (0x67 :: 0xF7 :: am.modrm 7 :: am.tail))
      (Effect.post (idivM32A32Effect p (3 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [idivM32A32Effect_components]; simp [Component.Covers]) _)
    (idiv_m32_a32_effect_step p am hv hx hb)

theorem idiv_m32_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧
      IdivDefined ((Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s)
            (
              (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand 32).read s))
      (codeRange p (0x67 :: rex :: 0xF7 :: am.modrm 7 :: am.tail))
      (idivM32A32Effect p (4 + am.tail.length) am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, hread⟩, hdef⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := idiv_m_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread) (by rw [hsc]; exact hdef)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 6 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 6 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [idivSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch, mergeGPR_32]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact idiv_divFlags_allows _ _ _

theorem idiv_m32_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧
      IdivDefined ((Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s)
            (
              (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand 32).read s))
      (codeRange p (0x67 :: rex :: 0xF7 :: am.modrm 7 :: am.tail))
      (Effect.post (idivM32A32Effect p (4 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [idivM32A32Effect_components]; simp [Component.Covers]) _)
    (idiv_m32_rex_a32_effect_step p rex hrex am hv hx hb)

theorem idiv_m16_a32_effect_step [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
      IdivDefined ((Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s)
            (
              (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand 16).read s))
      (codeRange p (0x67 :: 0x66 :: 0xF7 :: am.modrm 7 :: am.tail))
      (idivM16A32Effect p (4 + am.tail.length) am) := by
  rintro s h hcode ⟨⟨hp, hread⟩, hdef⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66]) := by
    rw [scanContext_asz_cons]
  have hstep := idiv_m16_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread) (by rw [hsc]; exact hdef)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 6 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 6 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [idivSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact idiv_divFlags_allows _ _ _

theorem idiv_m16_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
      IdivDefined ((Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s)
            (
              (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand 16).read s))
      (codeRange p (0x67 :: 0x66 :: 0xF7 :: am.modrm 7 :: am.tail))
      (Effect.post (idivM16A32Effect p (4 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [idivM16A32Effect_components]; simp [Component.Covers]) _)
    (idiv_m16_a32_effect_step p am hv hx hb)

theorem idiv_m16_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (5 + am.tail.length))) 2 s ∧
      IdivDefined ((Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s)
            (
              (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) : Operand 16).read s))
      (codeRange p (0x67 :: 0x66 :: rex :: 0xF7 :: am.modrm 7 :: am.tail))
      (idivM16A32Effect p (5 + am.tail.length) am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, hread⟩, hdef⟩
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66, rex] =
      withAsz (oszRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_66_rex _ _ hr]
  have hstep := idiv_m16_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread) (by rw [hsc]; exact hdef)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWritePairOutputs h _ _ _ _ _ _ 6 _,
    ⟨afterStep_loadWritePairOutputs_rip h _ _ _ _ _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWritePairOutputs s _ _ _ _ _ _ 6 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [idivSpec, Operand.read_reg_dataAccess, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    exact ⟨rfl, rfl⟩
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact idiv_divFlags_allows _ _ _

theorem idiv_m16_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (5 + am.tail.length))) 2 s ∧
      IdivDefined ((Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s)
            (
              (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) : Operand 16).read s))
      (codeRange p (0x67 :: 0x66 :: rex :: 0xF7 :: am.modrm 7 :: am.tail))
      (Effect.post (idivM16A32Effect p (5 + am.tail.length) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [idivM16A32Effect_components]; simp [Component.Covers]) _)
    (idiv_m16_rex_a32_effect_step p rex hrex am hv hx hb)

theorem idiv_m64_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (3 + am.tail.length))) 8 s ∧
      IdivDefined ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s)
            (
              (Operand.mem (am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) : Operand 64).read s))
      (codeRange p (encodeIdivM64 am))
      (Effect.post (idivM64Effect p (3 + am.tail.length) am)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact idiv_m64_triple_of_bytes p _ hrex am hv hx hb

theorem idiv_m32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (encodeIdivM32 am).length)) 4 s ∧
      IdivDefined ((Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s)
            (
              (Operand.mem (am.addr s (p + BitVec.ofNat 64 (encodeIdivM32 am).length)) : Operand 32).read s))
      (codeRange p (encodeIdivM32 am))
      (Effect.post (idivM32Effect p (encodeIdivM32 am).length am)) := by
  unfold encodeIdivM32
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := idiv_m32_triple_of_bytes p am hv hx hb
    rwa [show (0xF7 :: am.modrm 7 :: am.tail).length =
      2 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := idiv_m32_rex_triple_of_bytes p _ hrex am hv hx hb
    rwa [show (am.rexByte false 0 :: 0xF7 :: am.modrm 7 :: am.tail).length =
      3 + am.tail.length by simp; omega]

theorem idiv_m16_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (fun s => LoadPre p (fun u => am.addr u (p + BitVec.ofNat 64 (encodeIdivM16 am).length)) 2 s ∧
      IdivDefined ((Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s)
            (
              (Operand.mem (am.addr s (p + BitVec.ofNat 64 (encodeIdivM16 am).length)) : Operand 16).read s))
      (codeRange p (encodeIdivM16 am))
      (Effect.post (idivM16Effect p (encodeIdivM16 am).length am)) := by
  unfold encodeIdivM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := idiv_m16_triple_of_bytes p am hv hx hb
    rwa [show (0x66 :: 0xF7 :: am.modrm 7 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := idiv_m16_rex_triple_of_bytes p _ hrex am hv hx hb
    rwa [show (0x66 :: am.rexByte false 0 :: 0xF7 :: am.modrm 7 :: am.tail).length =
      4 + am.tail.length by simp; omega]

theorem idiv_m64_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (fun s => SegLoadPre p r base (fun u => am.addr u (p + BitVec.ofNat 64 (4 + am.tail.length))) 8 s ∧
      IdivDefined ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s)
            (
              (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand 64).read s))
      (codeRange p (r.prefixByte :: encodeIdivM64 am))
      (Effect.post (idivM64SegEffect p (4 + am.tail.length) base am)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact idiv_m64_seg_triple_of_bytes p r base _ hrex am hv hx hb

theorem idiv_m32_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (fun s => SegLoadPre p r base (fun u => am.addr u (p + BitVec.ofNat 64 (r.prefixByte :: encodeIdivM32 am).length)) 4 s ∧
      IdivDefined ((Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s)
            (
              (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeIdivM32 am).length)) : Operand 32).read s))
      (codeRange p (r.prefixByte :: encodeIdivM32 am))
      (Effect.post (idivM32SegEffect p (r.prefixByte :: encodeIdivM32 am).length base
        am)) := by
  unfold encodeIdivM32
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := idiv_m32_seg_triple_of_bytes p r base am hv hx hb
    rwa [show (r.prefixByte :: 0xF7 :: am.modrm 7 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := idiv_m32_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb
    rwa [show (r.prefixByte :: am.rexByte false 0 :: 0xF7 :: am.modrm 7 ::
      am.tail).length = 4 + am.tail.length by simp; omega]

theorem idiv_m16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (fun s => SegLoadPre p r base (fun u => am.addr u (p + BitVec.ofNat 64 (r.prefixByte :: encodeIdivM16 am).length)) 2 s ∧
      IdivDefined ((Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s)
            (
              (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeIdivM16 am).length)) : Operand 16).read s))
      (codeRange p (r.prefixByte :: encodeIdivM16 am))
      (Effect.post (idivM16SegEffect p (r.prefixByte :: encodeIdivM16 am).length base
        am)) := by
  unfold encodeIdivM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := idiv_m16_seg_triple_of_bytes p r base am hv hx hb
    rwa [show (r.prefixByte :: 0x66 :: 0xF7 :: am.modrm 7 :: am.tail).length =
      4 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := idiv_m16_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb
    rwa [show (r.prefixByte :: 0x66 :: am.rexByte false 0 :: 0xF7 :: am.modrm 7 ::
      am.tail).length = 5 + am.tail.length by simp; omega]

theorem idiv_m64_a32_triple [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (4 + am.tail.length))) 8 s ∧
      IdivDefined ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s)
            (
              (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) : Operand 64).read s))
      (codeRange p (0x67 :: encodeIdivM64 am))
      (Effect.post (idivM64A32Effect p (4 + am.tail.length) am)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact idiv_m64_a32_triple_of_bytes p _ hrex am hv hx hb

theorem idiv_m32_a32_triple [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (0x67 :: encodeIdivM32 am).length)) 4 s ∧
      IdivDefined ((Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s)
            (
              (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeIdivM32 am).length)) : Operand 32).read s))
      (codeRange p (0x67 :: encodeIdivM32 am))
      (Effect.post (idivM32A32Effect p (0x67 :: encodeIdivM32 am).length
        am)) := by
  unfold encodeIdivM32
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := idiv_m32_a32_triple_of_bytes p am hv hx hb
    rwa [show (0x67 :: 0xF7 :: am.modrm 7 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := idiv_m32_rex_a32_triple_of_bytes p _ hrex am hv hx hb
    rwa [show (0x67 :: am.rexByte false 0 :: 0xF7 :: am.modrm 7 ::
      am.tail).length = 4 + am.tail.length by simp; omega]

theorem idiv_m16_a32_triple [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple (fun s => LoadPre p (fun u => am.addr32 u (p + BitVec.ofNat 64 (0x67 :: encodeIdivM16 am).length)) 2 s ∧
      IdivDefined ((Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s)
            (
              (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeIdivM16 am).length)) : Operand 16).read s))
      (codeRange p (0x67 :: encodeIdivM16 am))
      (Effect.post (idivM16A32Effect p (0x67 :: encodeIdivM16 am).length
        am)) := by
  unfold encodeIdivM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := idiv_m16_a32_triple_of_bytes p am hv hx hb
    rwa [show (0x67 :: 0x66 :: 0xF7 :: am.modrm 7 :: am.tail).length =
      4 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := idiv_m16_rex_a32_triple_of_bytes p _ hrex am hv hx hb
    rwa [show (0x67 :: 0x66 :: am.rexByte false 0 :: 0xF7 :: am.modrm 7 ::
      am.tail).length = 5 + am.tail.length by simp; omega]

attribute [x86_compose] idivM64Effect idivM32Effect idivM16Effect idivM64SegEffect idivM32SegEffect idivM16SegEffect idivM64A32Effect idivM32A32Effect idivM16A32Effect

@[x86_local] theorem idivM64Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (idivM64Effect p len am) := by
  effect_local [idivM64Effect, divFlags]

@[x86_local] theorem idivM64SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} : Effect.Local (idivM64SegEffect p len base am) := by
  effect_local [idivM64SegEffect, divFlags]

@[x86_local] theorem idivM64A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (idivM64A32Effect p len am) := by
  effect_local [idivM64A32Effect, divFlags]

@[x86_local] theorem idivM32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (idivM32Effect p len am) := by
  effect_local [idivM32Effect, divFlags]

@[x86_local] theorem idivM32SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} : Effect.Local (idivM32SegEffect p len base am) := by
  effect_local [idivM32SegEffect, divFlags]

@[x86_local] theorem idivM32A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (idivM32A32Effect p len am) := by
  effect_local [idivM32A32Effect, divFlags]

@[x86_local] theorem idivM16Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (idivM16Effect p len am) := by
  effect_local [idivM16Effect, divFlags]

@[x86_local] theorem idivM16SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} : Effect.Local (idivM16SegEffect p len base am) := by
  effect_local [idivM16SegEffect, divFlags]

@[x86_local] theorem idivM16A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (idivM16A32Effect p len am) := by
  effect_local [idivM16A32Effect, divFlags]

end X86Proofs
