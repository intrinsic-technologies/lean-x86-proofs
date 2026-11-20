import X86Proofs.Instructions.Lzcnt.Generated.RM.Step
import X86Proofs.Instructions.Lzcnt.Generated.RM.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.ReadWrite.LoadFlags
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def lzcntR64M64Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let x := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      BitVec.ofNat 64 (leadingZeros x)⟩]
    flags := some (lzcntFlags x) }

@[simp] theorem lzcntR64M64Effect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (lzcntR64M64Effect p len dst am s).components = [.reg dst, .flags, .rip] := rfl

def lzcntR64M64SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let x := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      BitVec.ofNat 64 (leadingZeros x)⟩]
    flags := some (lzcntFlags x) }

@[simp] theorem lzcntR64M64SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (lzcntR64M64SegEffect p len base dst am s).components = [.reg dst, .flags, .rip] := rfl

def lzcntR64M64A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let x := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      BitVec.ofNat 64 (leadingZeros x)⟩]
    flags := some (lzcntFlags x) }

@[simp] theorem lzcntR64M64A32Effect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (lzcntR64M64A32Effect p len dst am s).components = [.reg dst, .flags, .rip] := rfl

def lzcntR32M32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let x := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      (BitVec.ofNat 32 (leadingZeros x)).setWidth 64⟩]
    flags := some (lzcntFlags x) }

@[simp] theorem lzcntR32M32Effect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (lzcntR32M32Effect p len dst am s).components = [.reg dst, .flags, .rip] := rfl

def lzcntR32M32SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let x := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      (BitVec.ofNat 32 (leadingZeros x)).setWidth 64⟩]
    flags := some (lzcntFlags x) }

@[simp] theorem lzcntR32M32SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (lzcntR32M32SegEffect p len base dst am s).components = [.reg dst, .flags, .rip] := rfl

def lzcntR32M32A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let x := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      (BitVec.ofNat 32 (leadingZeros x)).setWidth 64⟩]
    flags := some (lzcntFlags x) }

@[simp] theorem lzcntR32M32A32Effect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (lzcntR32M32A32Effect p len dst am s).components = [.reg dst, .flags, .rip] := rfl

def lzcntR16M16Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let x := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (BitVec.ofNat 16 (leadingZeros x)) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (lzcntFlags x) }

@[simp] theorem lzcntR16M16Effect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (lzcntR16M16Effect p len dst am s).components = [.reg dst, .flags, .rip] := rfl

def lzcntR16M16SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let x := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (BitVec.ofNat 16 (leadingZeros x)) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (lzcntFlags x) }

@[simp] theorem lzcntR16M16SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (lzcntR16M16SegEffect p len base dst am s).components = [.reg dst, .flags, .rip] := rfl

def lzcntR16M16A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let x := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (BitVec.ofNat 16 (leadingZeros x)) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (lzcntFlags x) }

@[simp] theorem lzcntR16M16A32Effect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (lzcntR16M16A32Effect p len dst am s).components = [.reg dst, .flags, .rip] := rfl

theorem lzcnt_r64_m64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (0xF3 :: rex :: 0x0F :: 0xBD :: am.modrm reg :: am.tail))
      (lzcntR64M64Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, hread⟩, hl⟩
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := lzcnt_r_m_step s h [0xF3, rex] (by simp [scanPrefix_f3, hr.scanPrefix]) (by simp) 64 (.inl rfl)
    (by rw [scanContext_f3_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_f3_rex _ _ hr]; rfl) (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl) (by rw [scanContext_f3_rex _ _ hr]; rfl) hl reg am hv
    (by rw [scanContext_f3_rex _ _ hr]; exact (AddrContext.repRex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_f3_rex _ _ hr]; exact hread)
  simp only [scanContext_f3_rex _ _ hr] at hstep
  have hdst : gprNumber (repRexContext s.DS rex.toBitVec).rex_r4 (repRexContext s.DS rex.toBitVec).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, lzcntSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact lzcntFlags_allows _ _

theorem lzcnt_r64_m64_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (0xF3 :: rex :: 0x0F :: 0xBD :: am.modrm reg :: am.tail))
      (Effect.post (lzcntR64M64Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lzcntR64M64Effect_components]; simp [Component.Covers]) _)
    (lzcnt_r64_m64_effect_step p rex hrex reg am hv hx hb)

theorem lzcnt_r32_m32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (fun s => LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (0xF3 :: 0x0F :: 0xBD :: am.modrm reg :: am.tail))
      (lzcntR32M32Effect p (4 + am.tail.length)
        (gprNumber 0 0 reg) am) := by
  rintro s h hcode ⟨⟨hp, hread⟩, hl⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := lzcnt_r_m_step s h [0xF3] (by simpa using scanPrefix_f3) (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) (by rfl) hl reg am hv
    (by exact (AddrContext.rep _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0xF3]).rex_r4 (scanContext s.DS (PrefixSegments.ofState s) [0xF3]).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, lzcntSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact lzcntFlags_allows _ _

theorem lzcnt_r32_m32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (fun s => LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (0xF3 :: 0x0F :: 0xBD :: am.modrm reg :: am.tail))
      (Effect.post (lzcntR32M32Effect p (4 + am.tail.length)
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lzcntR32M32Effect_components]; simp [Component.Covers]) _)
    (lzcnt_r32_m32_effect_step p reg am hv hx hb)

theorem lzcnt_r32_m32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (0xF3 :: rex :: 0x0F :: 0xBD :: am.modrm reg :: am.tail))
      (lzcntR32M32Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, hread⟩, hl⟩
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := lzcnt_r_m_step s h [0xF3, rex] (by simp [scanPrefix_f3, hr.scanPrefix]) (by simp) 32 (.inr rfl)
    (by rw [scanContext_f3_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_f3_rex _ _ hr]; rfl) (by rw [scanContext_f3_rex _ _ hr]; rfl)
    (by rw [scanContext_f3_rex _ _ hr]; rfl) (by rw [scanContext_f3_rex _ _ hr]; rfl) hl reg am hv
    (by rw [scanContext_f3_rex _ _ hr]; exact (AddrContext.repRex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_f3_rex _ _ hr]; exact hread)
  simp only [scanContext_f3_rex _ _ hr] at hstep
  have hdst : gprNumber (repRexContext s.DS rex.toBitVec).rex_r4 (repRexContext s.DS rex.toBitVec).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, lzcntSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact lzcntFlags_allows _ _

theorem lzcnt_r32_m32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (0xF3 :: rex :: 0x0F :: 0xBD :: am.modrm reg :: am.tail))
      (Effect.post (lzcntR32M32Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lzcntR32M32Effect_components]; simp [Component.Covers]) _)
    (lzcnt_r32_m32_rex_effect_step p rex hrex reg am hv hx hb)

theorem lzcnt_r16_m16_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (fun s => LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (0x66 :: 0xF3 :: 0x0F :: 0xBD :: am.modrm reg :: am.tail))
      (lzcntR16M16Effect p (5 + am.tail.length)
        (gprNumber 0 0 reg) am) := by
  rintro s h hcode ⟨⟨hp, hread⟩, hl⟩
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := lzcnt_r16_m16_step s h [0x66, 0xF3] (by simp [scanPrefix_66, scanPrefix_f3]) (by simp)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) (by rfl) hl reg am hv
    (by exact (AddrContext.oszRep _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66, 0xF3]).rex_r4 (scanContext s.DS (PrefixSegments.ofState s) [0x66, 0xF3]).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, lzcntSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact lzcntFlags_allows _ _

theorem lzcnt_r16_m16_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (fun s => LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (0x66 :: 0xF3 :: 0x0F :: 0xBD :: am.modrm reg :: am.tail))
      (Effect.post (lzcntR16M16Effect p (5 + am.tail.length)
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lzcntR16M16Effect_components]; simp [Component.Covers]) _)
    (lzcnt_r16_m16_effect_step p reg am hv hx hb)

theorem lzcnt_r64_m64_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 8 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (r.prefixByte :: 0xF3 :: rex :: 0x0F :: 0xBD :: am.modrm reg :: am.tail))
      (lzcntR64M64SegEffect p (6 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, ⟨hseg, hbase⟩, hread⟩, hl⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3, rex] =
      withSeg (repRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3, rex]
      (noSegPrefix_cons noSegPrefix_f3 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_f3_rex _ _ hr]
  have hstep := lzcnt_r_m_step s h [r.prefixByte, 0xF3, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_f3, hr.scanPrefix])) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) hl reg am hv
    (by rw [hsc]; exact (AddrContext.repRex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (repRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4 (withSeg (repRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, lzcntSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact lzcntFlags_allows _ _

theorem lzcnt_r64_m64_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 8 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (r.prefixByte :: 0xF3 :: rex :: 0x0F :: 0xBD :: am.modrm reg :: am.tail))
      (Effect.post (lzcntR64M64SegEffect p (6 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lzcntR64M64SegEffect_components]; simp [Component.Covers]) _)
    (lzcnt_r64_m64_seg_effect_step p r base rex hrex reg am hv hx hb)

theorem lzcnt_r32_m32_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (fun s => SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (r.prefixByte :: 0xF3 :: 0x0F :: 0xBD :: am.modrm reg :: am.tail))
      (lzcntR32M32SegEffect p (5 + am.tail.length) base (gprNumber 0 0 reg) am) := by
  rintro s h hcode ⟨⟨hp, ⟨hseg, hbase⟩, hread⟩, hl⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3]
      (noSegPrefix_cons noSegPrefix_f3 noSegPrefix_nil)]
  have hstep := lzcnt_r_m_step s h [r.prefixByte, 0xF3] (scanPrefix_seg_cons r (by simpa using scanPrefix_f3)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) hl reg am hv
    (by rw [hsc]; exact (AddrContext.rep _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3]) (r.select (PrefixSegments.ofState s))).rex_r4 (withSeg (scanContext s.DS (PrefixSegments.ofState s) [0xF3]) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, lzcntSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact lzcntFlags_allows _ _

theorem lzcnt_r32_m32_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (fun s => SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (r.prefixByte :: 0xF3 :: 0x0F :: 0xBD :: am.modrm reg :: am.tail))
      (Effect.post (lzcntR32M32SegEffect p (5 + am.tail.length) base (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lzcntR32M32SegEffect_components]; simp [Component.Covers]) _)
    (lzcnt_r32_m32_seg_effect_step p r base reg am hv hx hb)

theorem lzcnt_r32_m32_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 4 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (r.prefixByte :: 0xF3 :: rex :: 0x0F :: 0xBD :: am.modrm reg :: am.tail))
      (lzcntR32M32SegEffect p (6 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, ⟨hseg, hbase⟩, hread⟩, hl⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0xF3, rex] =
      withSeg (repRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0xF3, rex]
      (noSegPrefix_cons noSegPrefix_f3 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_f3_rex _ _ hr]
  have hstep := lzcnt_r_m_step s h [r.prefixByte, 0xF3, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_f3, hr.scanPrefix])) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) hl reg am hv
    (by rw [hsc]; exact (AddrContext.repRex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (repRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4 (withSeg (repRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, lzcntSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact lzcntFlags_allows _ _

theorem lzcnt_r32_m32_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 4 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (r.prefixByte :: 0xF3 :: rex :: 0x0F :: 0xBD :: am.modrm reg :: am.tail))
      (Effect.post (lzcntR32M32SegEffect p (6 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lzcntR32M32SegEffect_components]; simp [Component.Covers]) _)
    (lzcnt_r32_m32_rex_seg_effect_step p r base rex hrex reg am hv hx hb)

theorem lzcnt_r16_m16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (fun s => SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (r.prefixByte :: 0x66 :: 0xF3 :: 0x0F :: 0xBD :: am.modrm reg :: am.tail))
      (lzcntR16M16SegEffect p (6 + am.tail.length) base (gprNumber 0 0 reg) am) := by
  rintro s h hcode ⟨⟨hp, ⟨hseg, hbase⟩, hread⟩, hl⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66, 0xF3] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66, 0xF3]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66, 0xF3]
      (noSegPrefix_cons noSegPrefix_66 (noSegPrefix_cons noSegPrefix_f3 noSegPrefix_nil))]
  have hstep := lzcnt_r16_m16_step s h [r.prefixByte, 0x66, 0xF3] (scanPrefix_seg_cons r (by simp [scanPrefix_66, scanPrefix_f3])) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) hl reg am hv
    (by rw [hsc]; exact (AddrContext.oszRep _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66, 0xF3]) (r.select (PrefixSegments.ofState s))).rex_r4 (withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66, 0xF3]) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, lzcntSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact lzcntFlags_allows _ _

theorem lzcnt_r16_m16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (fun s => SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (r.prefixByte :: 0x66 :: 0xF3 :: 0x0F :: 0xBD :: am.modrm reg :: am.tail))
      (Effect.post (lzcntR16M16SegEffect p (6 + am.tail.length) base (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lzcntR16M16SegEffect_components]; simp [Component.Covers]) _)
    (lzcnt_r16_m16_seg_effect_step p r base reg am hv hx hb)

theorem lzcnt_r64_m64_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 8 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (0x67 :: 0xF3 :: rex :: 0x0F :: 0xBD :: am.modrm reg :: am.tail))
      (lzcntR64M64A32Effect p (6 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, hread⟩, hl⟩
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0xF3, rex] =
      withAsz (repRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]
  have hstep := lzcnt_r_m_a32_step s h [0x67, 0xF3, rex] (scanPrefix_asz_cons (by simp [scanPrefix_f3, hr.scanPrefix])) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) hl reg am hv
    (by rw [hsc]; exact (AddrContext.repRex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (repRexContext s.DS rex.toBitVec)).rex_r4 (withAsz (repRexContext s.DS rex.toBitVec)).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, lzcntSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact lzcntFlags_allows _ _

theorem lzcnt_r64_m64_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 8 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (0x67 :: 0xF3 :: rex :: 0x0F :: 0xBD :: am.modrm reg :: am.tail))
      (Effect.post (lzcntR64M64A32Effect p (6 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lzcntR64M64A32Effect_components]; simp [Component.Covers]) _)
    (lzcnt_r64_m64_a32_effect_step p rex hrex reg am hv hx hb)

theorem lzcnt_r32_m32_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (fun s => LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (0x67 :: 0xF3 :: 0x0F :: 0xBD :: am.modrm reg :: am.tail))
      (lzcntR32M32A32Effect p (5 + am.tail.length)
        (gprNumber 0 0 reg) am) := by
  rintro s h hcode ⟨⟨hp, hread⟩, hl⟩
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0xF3] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) [0xF3]) := by
    rw [scanContext_asz_cons]
  have hstep := lzcnt_r_m_a32_step s h [0x67, 0xF3] (scanPrefix_asz_cons (by simpa using scanPrefix_f3)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) hl reg am hv
    (by rw [hsc]; exact (AddrContext.rep _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0xF3])).rex_r4 (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0xF3])).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, lzcntSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact lzcntFlags_allows _ _

theorem lzcnt_r32_m32_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (fun s => LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (0x67 :: 0xF3 :: 0x0F :: 0xBD :: am.modrm reg :: am.tail))
      (Effect.post (lzcntR32M32A32Effect p (5 + am.tail.length)
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lzcntR32M32A32Effect_components]; simp [Component.Covers]) _)
    (lzcnt_r32_m32_a32_effect_step p reg am hv hx hb)

theorem lzcnt_r32_m32_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 4 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (0x67 :: 0xF3 :: rex :: 0x0F :: 0xBD :: am.modrm reg :: am.tail))
      (lzcntR32M32A32Effect p (6 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, hread⟩, hl⟩
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0xF3, rex] =
      withAsz (repRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_f3_rex _ _ hr]
  have hstep := lzcnt_r_m_a32_step s h [0x67, 0xF3, rex] (scanPrefix_asz_cons (by simp [scanPrefix_f3, hr.scanPrefix])) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) hl reg am hv
    (by rw [hsc]; exact (AddrContext.repRex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (repRexContext s.DS rex.toBitVec)).rex_r4 (withAsz (repRexContext s.DS rex.toBitVec)).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, lzcntSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact lzcntFlags_allows _ _

theorem lzcnt_r32_m32_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 4 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (0x67 :: 0xF3 :: rex :: 0x0F :: 0xBD :: am.modrm reg :: am.tail))
      (Effect.post (lzcntR32M32A32Effect p (6 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lzcntR32M32A32Effect_components]; simp [Component.Covers]) _)
    (lzcnt_r32_m32_rex_a32_effect_step p rex hrex reg am hv hx hb)

theorem lzcnt_r16_m16_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (fun s => LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (0x67 :: 0x66 :: 0xF3 :: 0x0F :: 0xBD :: am.modrm reg :: am.tail))
      (lzcntR16M16A32Effect p (6 + am.tail.length)
        (gprNumber 0 0 reg) am) := by
  rintro s h hcode ⟨⟨hp, hread⟩, hl⟩
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66, 0xF3] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66, 0xF3]) := by
    rw [scanContext_asz_cons]
  have hstep := lzcnt_r16_m16_a32_step s h [0x67, 0x66, 0xF3] (scanPrefix_asz_cons (by simp [scanPrefix_66, scanPrefix_f3])) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) hl reg am hv
    (by rw [hsc]; exact (AddrContext.oszRep _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66, 0xF3])).rex_r4 (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66, 0xF3])).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, lzcntSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact lzcntFlags_allows _ _

theorem lzcnt_r16_m16_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (fun s => LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (0x67 :: 0x66 :: 0xF3 :: 0x0F :: 0xBD :: am.modrm reg :: am.tail))
      (Effect.post (lzcntR16M16A32Effect p (6 + am.tail.length)
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lzcntR16M16A32Effect_components]; simp [Component.Covers]) _)
    (lzcnt_r16_m16_a32_effect_step p reg am hv hx hb)

theorem lzcnt_r64_m64_triple [Bindings] (p : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (fun s => LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (encodeLzcntR64M64 dst am).length)) 8 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (encodeLzcntR64M64 dst am))
      (Effect.post (lzcntR64M64Effect p (encodeLzcntR64M64 dst am).length (dst.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := lzcnt_r64_m64_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
  rw [hr, gprNumber_reg] at this
  unfold encodeLzcntR64M64
  rw [show (0xF3 :: am.rexByte true dst :: 0x0F :: 0xBD :: am.modrm (regLow dst) ::
    am.tail).length = 5 + am.tail.length by simp; omega]
  exact this

theorem lzcnt_r64_m64_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (fun s => SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeLzcntR64M64 dst am).length)) 8 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (r.prefixByte :: encodeLzcntR64M64 dst am))
      (Effect.post (lzcntR64M64SegEffect p (r.prefixByte :: encodeLzcntR64M64 dst am).length base (dst.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := lzcnt_r64_m64_seg_triple_of_bytes p r base _ hrex (regLow dst) am hv hx hb
  rw [hr, gprNumber_reg] at this
  unfold encodeLzcntR64M64
  rw [show (r.prefixByte :: 0xF3 :: am.rexByte true dst :: 0x0F :: 0xBD :: am.modrm (regLow dst) ::
    am.tail).length = 6 + am.tail.length by simp; omega]
  exact this

theorem lzcnt_r64_m64_a32_triple [Bindings] (p : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (fun s => LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeLzcntR64M64 dst am).length)) 8 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (0x67 :: encodeLzcntR64M64 dst am))
      (Effect.post (lzcntR64M64A32Effect p (0x67 :: encodeLzcntR64M64 dst am).length (dst.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := lzcnt_r64_m64_a32_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
  rw [hr, gprNumber_reg] at this
  unfold encodeLzcntR64M64
  rw [show (0x67 :: 0xF3 :: am.rexByte true dst :: 0x0F :: 0xBD :: am.modrm (regLow dst) ::
    am.tail).length = 6 + am.tail.length by simp; omega]
  exact this

theorem lzcnt_r32_m32_triple [Bindings] (p : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (fun s => LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (encodeLzcntR32M32 dst am).length)) 4 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (encodeLzcntR32M32 dst am))
      (Effect.post (lzcntR32M32Effect p (encodeLzcntR32M32 dst am).length (dst.setWidth 5) am)) := by
  unfold encodeLzcntR32M32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := lzcnt_r32_m32_triple_of_bytes p (regLow dst) am hv hx hb
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    rw [show (0xF3 :: 0x0F :: 0xBD :: am.modrm (regLow dst) :: am.tail).length =
      4 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := lzcnt_r32_m32_rex_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    rw [show (0xF3 :: am.rexByte false dst :: 0x0F :: 0xBD :: am.modrm (regLow dst) ::
      am.tail).length = 5 + am.tail.length by simp; omega]
    exact this

theorem lzcnt_r32_m32_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (fun s => SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeLzcntR32M32 dst am).length)) 4 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (r.prefixByte :: encodeLzcntR32M32 dst am))
      (Effect.post (lzcntR32M32SegEffect p (r.prefixByte :: encodeLzcntR32M32 dst am).length base (dst.setWidth 5) am)) := by
  unfold encodeLzcntR32M32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := lzcnt_r32_m32_seg_triple_of_bytes p r base (regLow dst) am hv hx hb
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    rw [show (r.prefixByte :: 0xF3 :: 0x0F :: 0xBD :: am.modrm (regLow dst) :: am.tail).length =
      5 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := lzcnt_r32_m32_rex_seg_triple_of_bytes p r base _ hrex (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    rw [show (r.prefixByte :: 0xF3 :: am.rexByte false dst :: 0x0F :: 0xBD :: am.modrm (regLow dst) ::
      am.tail).length = 6 + am.tail.length by simp; omega]
    exact this

theorem lzcnt_r32_m32_a32_triple [Bindings] (p : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (fun s => LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeLzcntR32M32 dst am).length)) 4 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (0x67 :: encodeLzcntR32M32 dst am))
      (Effect.post (lzcntR32M32A32Effect p (0x67 :: encodeLzcntR32M32 dst am).length (dst.setWidth 5) am)) := by
  unfold encodeLzcntR32M32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := lzcnt_r32_m32_a32_triple_of_bytes p (regLow dst) am hv hx hb
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    rw [show (0x67 :: 0xF3 :: 0x0F :: 0xBD :: am.modrm (regLow dst) :: am.tail).length =
      5 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := lzcnt_r32_m32_rex_a32_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    rw [show (0x67 :: 0xF3 :: am.rexByte false dst :: 0x0F :: 0xBD :: am.modrm (regLow dst) ::
      am.tail).length = 6 + am.tail.length by simp; omega]
    exact this

theorem lzcnt_r16_m16_triple [Bindings] (p : BitVec 64)
    (dst : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (fun s => LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (encodeLzcntR16M16 dst am).length)) 2 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (encodeLzcntR16M16 dst am))
      (Effect.post (lzcntR16M16Effect p (encodeLzcntR16M16 dst am).length (dst.setWidth 5) am)) := by
  have := lzcnt_r16_m16_triple_of_bytes p dst am hv hx hb
  rw [gprNumber_zero_zero] at this
  unfold encodeLzcntR16M16
  rw [show (0x66 :: 0xF3 :: 0x0F :: 0xBD :: am.modrm dst :: am.tail).length =
    5 + am.tail.length by simp; omega]
  exact this

theorem lzcnt_r16_m16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (fun s => SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeLzcntR16M16 dst am).length)) 2 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (r.prefixByte :: encodeLzcntR16M16 dst am))
      (Effect.post (lzcntR16M16SegEffect p (r.prefixByte :: encodeLzcntR16M16 dst am).length base (dst.setWidth 5) am)) := by
  have := lzcnt_r16_m16_seg_triple_of_bytes p r base dst am hv hx hb
  rw [gprNumber_zero_zero] at this
  unfold encodeLzcntR16M16
  rw [show (r.prefixByte :: 0x66 :: 0xF3 :: 0x0F :: 0xBD :: am.modrm dst :: am.tail).length =
    6 + am.tail.length by simp; omega]
  exact this

theorem lzcnt_r16_m16_a32_triple [Bindings] (p : BitVec 64)
    (dst : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (fun s => LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeLzcntR16M16 dst am).length)) 2 s ∧
      Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p (0x67 :: encodeLzcntR16M16 dst am))
      (Effect.post (lzcntR16M16A32Effect p (0x67 :: encodeLzcntR16M16 dst am).length (dst.setWidth 5) am)) := by
  have := lzcnt_r16_m16_a32_triple_of_bytes p dst am hv hx hb
  rw [gprNumber_zero_zero] at this
  unfold encodeLzcntR16M16
  rw [show (0x67 :: 0x66 :: 0xF3 :: 0x0F :: 0xBD :: am.modrm dst :: am.tail).length =
    6 + am.tail.length by simp; omega]
  exact this

attribute [x86_compose] lzcntR64M64Effect lzcntR32M32Effect lzcntR16M16Effect lzcntR64M64SegEffect lzcntR32M32SegEffect lzcntR16M16SegEffect lzcntR64M64A32Effect lzcntR32M32A32Effect lzcntR16M16A32Effect lzcntFlags

@[x86_local] theorem lzcntR64M64Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (lzcntR64M64Effect p len dst am) := by
  effect_local [lzcntR64M64Effect, lzcntFlags]

@[x86_local] theorem lzcntR64M64SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} :
    Effect.Local (lzcntR64M64SegEffect p len base dst am) := by
  effect_local [lzcntR64M64SegEffect, lzcntFlags]

@[x86_local] theorem lzcntR64M64A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (lzcntR64M64A32Effect p len dst am) := by
  effect_local [lzcntR64M64A32Effect, lzcntFlags]

@[x86_local] theorem lzcntR32M32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (lzcntR32M32Effect p len dst am) := by
  effect_local [lzcntR32M32Effect, lzcntFlags]

@[x86_local] theorem lzcntR32M32SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} :
    Effect.Local (lzcntR32M32SegEffect p len base dst am) := by
  effect_local [lzcntR32M32SegEffect, lzcntFlags]

@[x86_local] theorem lzcntR32M32A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (lzcntR32M32A32Effect p len dst am) := by
  effect_local [lzcntR32M32A32Effect, lzcntFlags]

@[x86_local] theorem lzcntR16M16Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (lzcntR16M16Effect p len dst am) := by
  effect_local [lzcntR16M16Effect, lzcntFlags]

@[x86_local] theorem lzcntR16M16SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} :
    Effect.Local (lzcntR16M16SegEffect p len base dst am) := by
  effect_local [lzcntR16M16SegEffect, lzcntFlags]

@[x86_local] theorem lzcntR16M16A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (lzcntR16M16A32Effect p len dst am) := by
  effect_local [lzcntR16M16A32Effect, lzcntFlags]

end X86Proofs
