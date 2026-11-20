import X86Proofs.Instructions.Imul.Generated.RMImm8.Step
import X86Proofs.Instructions.Imul.Generated.RMImm8.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def imulR64M64Imm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  let b := imm.signExtend 64
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      BitVec.ofInt 64 (a.toInt * b.toInt)⟩]
    flags := some (imulFlags a b) }

@[simp] theorem imulR64M64Imm8Effect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    (imulR64M64Imm8Effect p len dst am imm s).components = [.reg dst, .flags, .rip] := rfl

def imulR64M64Imm8SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  let b := imm.signExtend 64
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      BitVec.ofInt 64 (a.toInt * b.toInt)⟩]
    flags := some (imulFlags a b) }

@[simp] theorem imulR64M64Imm8SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    (imulR64M64Imm8SegEffect p len base dst am imm s).components = [.reg dst, .flags, .rip] := rfl

def imulR64M64Imm8A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  let b := imm.signExtend 64
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      BitVec.ofInt 64 (a.toInt * b.toInt)⟩]
    flags := some (imulFlags a b) }

@[simp] theorem imulR64M64Imm8A32Effect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    (imulR64M64Imm8A32Effect p len dst am imm s).components = [.reg dst, .flags, .rip] := rfl

def imulR32M32Imm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 32).read s
  let b := imm.signExtend 32
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      (BitVec.ofInt 32 (a.toInt * b.toInt)).setWidth 64⟩]
    flags := some (imulFlags a b) }

@[simp] theorem imulR32M32Imm8Effect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    (imulR32M32Imm8Effect p len dst am imm s).components = [.reg dst, .flags, .rip] := rfl

def imulR32M32Imm8SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 32).read s
  let b := imm.signExtend 32
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      (BitVec.ofInt 32 (a.toInt * b.toInt)).setWidth 64⟩]
    flags := some (imulFlags a b) }

@[simp] theorem imulR32M32Imm8SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    (imulR32M32Imm8SegEffect p len base dst am imm s).components = [.reg dst, .flags, .rip] := rfl

def imulR32M32Imm8A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 32).read s
  let b := imm.signExtend 32
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      (BitVec.ofInt 32 (a.toInt * b.toInt)).setWidth 64⟩]
    flags := some (imulFlags a b) }

@[simp] theorem imulR32M32Imm8A32Effect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    (imulR32M32Imm8A32Effect p len dst am imm s).components = [.reg dst, .flags, .rip] := rfl

def imulR16M16Imm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  let b := imm.signExtend 16
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (BitVec.ofInt 16 (a.toInt * b.toInt)) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (imulFlags a b) }

@[simp] theorem imulR16M16Imm8Effect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    (imulR16M16Imm8Effect p len dst am imm s).components = [.reg dst, .flags, .rip] := rfl

def imulR16M16Imm8SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  let b := imm.signExtend 16
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (BitVec.ofInt 16 (a.toInt * b.toInt)) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (imulFlags a b) }

@[simp] theorem imulR16M16Imm8SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    (imulR16M16Imm8SegEffect p len base dst am imm s).components = [.reg dst, .flags, .rip] := rfl

def imulR16M16Imm8A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (imm : BitVec 8) (s : RamState) : Effect :=
  let a := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  let b := imm.signExtend 16
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (BitVec.ofInt 16 (a.toInt * b.toInt)) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (imulFlags a b) }

@[simp] theorem imulR16M16Imm8A32Effect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    (imulR16M16Imm8A32Effect p len dst am imm s).components = [.reg dst, .flags, .rip] := rfl

theorem imul_r64_m64_imm8_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (rex :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (imulR64M64Imm8Effect p (4 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := imul_r_m_imm8_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_r4 (rexContext s.DS rex.toBitVec).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, imulSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulFlags_allows _ _ _

theorem imul_r64_m64_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (rex :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (imulR64M64Imm8Effect p (4 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulR64M64Imm8Effect_components]; simp [Component.Covers]) _)
    (imul_r64_m64_imm8_effect_step p rex hrex reg am hv hx hb imm)

theorem imul_r32_m32_imm8_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (imulR32M32Imm8Effect p (3 + am.tail.length)
        (gprNumber 0 0 reg) am imm) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := imul_r_m_imm8_step s h [] (by simp) (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) reg am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4 (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, imulSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulFlags_allows _ _ _

theorem imul_r32_m32_imm8_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (imulR32M32Imm8Effect p (3 + am.tail.length)
        (gprNumber 0 0 reg) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulR32M32Imm8Effect_components]; simp [Component.Covers]) _)
    (imul_r32_m32_imm8_effect_step p reg am hv hx hb imm)

theorem imul_r32_m32_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (rex :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (imulR32M32Imm8Effect p (4 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := imul_r_m_imm8_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_r4 (rexContext s.DS rex.toBitVec).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, imulSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulFlags_allows _ _ _

theorem imul_r32_m32_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (rex :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (imulR32M32Imm8Effect p (4 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulR32M32Imm8Effect_components]; simp [Component.Covers]) _)
    (imul_r32_m32_imm8_rex_effect_step p rex hrex reg am hv hx hb imm)

theorem imul_r16_m16_imm8_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (0x66 :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (imulR16M16Imm8Effect p (4 + am.tail.length)
        (gprNumber 0 0 reg) am imm) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := imul_r16_m16_imm8_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) reg am hv
    (by exact (AddrContext.osz _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r4 (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, imulSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulFlags_allows _ _ _

theorem imul_r16_m16_imm8_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (0x66 :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (imulR16M16Imm8Effect p (4 + am.tail.length)
        (gprNumber 0 0 reg) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulR16M16Imm8Effect_components]; simp [Component.Covers]) _)
    (imul_r16_m16_imm8_effect_step p reg am hv hx hb imm)

theorem imul_r16_m16_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (0x66 :: rex :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (imulR16M16Imm8Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := imul_r16_m16_imm8_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_66_rex _ _ hr]; exact (AddrContext.oszRex _ _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_66_rex _ _ hr]; exact hread)
  simp only [scanContext_66_rex _ _ hr] at hstep
  have hdst : gprNumber (oszRexContext s.DS rex.toBitVec).rex_r4 (oszRexContext s.DS rex.toBitVec).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, imulSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulFlags_allows _ _ _

theorem imul_r16_m16_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (0x66 :: rex :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (imulR16M16Imm8Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulR16M16Imm8Effect_components]; simp [Component.Covers]) _)
    (imul_r16_m16_imm8_rex_effect_step p rex hrex reg am hv hx hb imm)

theorem imul_r64_m64_imm8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
      (codeRange p (r.prefixByte :: rex :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (imulR64M64Imm8SegEffect p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := imul_r_m_imm8_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4 (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, imulSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulFlags_allows _ _ _

theorem imul_r64_m64_imm8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
      (codeRange p (r.prefixByte :: rex :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (imulR64M64Imm8SegEffect p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulR64M64Imm8SegEffect_components]; simp [Component.Covers]) _)
    (imul_r64_m64_imm8_seg_effect_step p r base rex hrex reg am hv hx hb imm)

theorem imul_r32_m32_imm8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (imulR32M32Imm8SegEffect p (4 + am.tail.length) base (gprNumber 0 0 reg) am imm) := by
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := imul_r_m_imm8_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r4 (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, imulSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulFlags_allows _ _ _

theorem imul_r32_m32_imm8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (imulR32M32Imm8SegEffect p (4 + am.tail.length) base (gprNumber 0 0 reg) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulR32M32Imm8SegEffect_components]; simp [Component.Covers]) _)
    (imul_r32_m32_imm8_seg_effect_step p r base reg am hv hx hb imm)

theorem imul_r32_m32_imm8_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: rex :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (imulR32M32Imm8SegEffect p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := imul_r_m_imm8_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4 (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, imulSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulFlags_allows _ _ _

theorem imul_r32_m32_imm8_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: rex :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (imulR32M32Imm8SegEffect p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulR32M32Imm8SegEffect_components]; simp [Component.Covers]) _)
    (imul_r32_m32_imm8_rex_seg_effect_step p r base rex hrex reg am hv hx hb imm)

theorem imul_r16_m16_imm8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (imulR16M16Imm8SegEffect p (5 + am.tail.length) base (gprNumber 0 0 reg) am imm) := by
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66]
      (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil)]
  have hstep := imul_r16_m16_imm8_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s))).rex_r4 (withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, imulSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulFlags_allows _ _ _

theorem imul_r16_m16_imm8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (imulR16M16Imm8SegEffect p (5 + am.tail.length) base (gprNumber 0 0 reg) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulR16M16Imm8SegEffect_components]; simp [Component.Covers]) _)
    (imul_r16_m16_imm8_seg_effect_step p r base reg am hv hx hb imm)

theorem imul_r16_m16_imm8_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (imulR16M16Imm8SegEffect p (6 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66, rex] =
      withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66, rex]
      (noSegPrefix_cons noSegPrefix_66 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_66_rex _ _ hr]
  have hstep := imul_r16_m16_imm8_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4 (withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, imulSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulFlags_allows _ _ _

theorem imul_r16_m16_imm8_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (imulR16M16Imm8SegEffect p (6 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulR16M16Imm8SegEffect_components]; simp [Component.Covers]) _)
    (imul_r16_m16_imm8_rex_seg_effect_step p r base rex hrex reg am hv hx hb imm)

theorem imul_r64_m64_imm8_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
      (codeRange p (0x67 :: rex :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (imulR64M64Imm8A32Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := imul_r_m_imm8_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (rexContext s.DS rex.toBitVec)).rex_r4 (withAsz (rexContext s.DS rex.toBitVec)).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, imulSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulFlags_allows _ _ _

theorem imul_r64_m64_imm8_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
      (codeRange p (0x67 :: rex :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (imulR64M64Imm8A32Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulR64M64Imm8A32Effect_components]; simp [Component.Covers]) _)
    (imul_r64_m64_imm8_a32_effect_step p rex hrex reg am hv hx hb imm)

theorem imul_r32_m32_imm8_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (0x67 :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (imulR32M32Imm8A32Effect p (4 + am.tail.length)
        (gprNumber 0 0 reg) am imm) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := imul_r_m_imm8_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r4 (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, imulSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulFlags_allows _ _ _

theorem imul_r32_m32_imm8_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (0x67 :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (imulR32M32Imm8A32Effect p (4 + am.tail.length)
        (gprNumber 0 0 reg) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulR32M32Imm8A32Effect_components]; simp [Component.Covers]) _)
    (imul_r32_m32_imm8_a32_effect_step p reg am hv hx hb imm)

theorem imul_r32_m32_imm8_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4)
      (codeRange p (0x67 :: rex :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (imulR32M32Imm8A32Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := imul_r_m_imm8_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (rexContext s.DS rex.toBitVec)).rex_r4 (withAsz (rexContext s.DS rex.toBitVec)).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, imulSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulFlags_allows _ _ _

theorem imul_r32_m32_imm8_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4)
      (codeRange p (0x67 :: rex :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (imulR32M32Imm8A32Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulR32M32Imm8A32Effect_components]; simp [Component.Covers]) _)
    (imul_r32_m32_imm8_rex_a32_effect_step p rex hrex reg am hv hx hb imm)

theorem imul_r16_m16_imm8_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (imulR16M16Imm8A32Effect p (5 + am.tail.length)
        (gprNumber 0 0 reg) am imm) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66]) := by
    rw [scanContext_asz_cons]
  have hstep := imul_r16_m16_imm8_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66])).rex_r4 (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66])).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, imulSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulFlags_allows _ _ _

theorem imul_r16_m16_imm8_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (imulR16M16Imm8A32Effect p (5 + am.tail.length)
        (gprNumber 0 0 reg) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulR16M16Imm8A32Effect_components]; simp [Component.Covers]) _)
    (imul_r16_m16_imm8_a32_effect_step p reg am hv hx hb imm)

theorem imul_r16_m16_imm8_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (imulR16M16Imm8A32Effect p (6 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66, rex] =
      withAsz (oszRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_66_rex _ _ hr]
  have hstep := imul_r16_m16_imm8_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (oszRexContext s.DS rex.toBitVec)).rex_r4 (withAsz (oszRexContext s.DS rex.toBitVec)).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteOutputs h _ _ _ _ _,
    ⟨afterStep_loadWriteOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, imulSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
    rfl
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact imulFlags_allows _ _ _

theorem imul_r16_m16_imm8_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x6B :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (imulR16M16Imm8A32Effect p (6 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [imulR16M16Imm8A32Effect_components]; simp [Component.Covers]) _)
    (imul_r16_m16_imm8_rex_a32_effect_step p rex hrex reg am hv hx hb imm)

theorem imul_r64_m64_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (encodeImulR64M64Imm8 dst am imm).length)) 8)
      (codeRange p (encodeImulR64M64Imm8 dst am imm))
      (Effect.post (imulR64M64Imm8Effect p (encodeImulR64M64Imm8 dst am imm).length (dst.setWidth 5) am imm)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := imul_r64_m64_imm8_triple_of_bytes p _ hrex (regLow dst) am hv hx hb imm
  rw [hr, gprNumber_reg] at this
  unfold encodeImulR64M64Imm8
  rw [show (am.rexByte true dst :: 0x6B :: am.modrm (regLow dst) :: (am.tail ++ immBytes 8 imm)).length =
    4 + am.tail.length by simp; omega]
  exact this

theorem imul_r32_m32_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (encodeImulR32M32Imm8 dst am imm).length)) 4)
      (codeRange p (encodeImulR32M32Imm8 dst am imm))
      (Effect.post (imulR32M32Imm8Effect p (encodeImulR32M32Imm8 dst am imm).length (dst.setWidth 5) am imm)) := by
  unfold encodeImulR32M32Imm8
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := imul_r32_m32_imm8_triple_of_bytes p (regLow dst) am hv hx hb imm
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    rw [show (0x6B :: am.modrm (regLow dst) :: (am.tail ++ immBytes 8 imm)).length =
      3 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := imul_r32_m32_imm8_rex_triple_of_bytes p _ hrex (regLow dst) am hv hx hb imm
    rw [hr, gprNumber_reg] at this
    rw [show (am.rexByte false dst :: 0x6B :: am.modrm (regLow dst) :: (am.tail ++ immBytes 8 imm)).length =
      4 + am.tail.length by simp; omega]
    exact this

theorem imul_r16_m16_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (encodeImulR16M16Imm8 dst am imm).length)) 2)
      (codeRange p (encodeImulR16M16Imm8 dst am imm))
      (Effect.post (imulR16M16Imm8Effect p (encodeImulR16M16Imm8 dst am imm).length (dst.setWidth 5) am imm)) := by
  unfold encodeImulR16M16Imm8
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := imul_r16_m16_imm8_triple_of_bytes p (regLow dst) am hv hx hb imm
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    rw [show (0x66 :: 0x6B :: am.modrm (regLow dst) :: (am.tail ++ immBytes 8 imm)).length =
      4 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := imul_r16_m16_imm8_rex_triple_of_bytes p _ hrex (regLow dst) am hv hx hb imm
    rw [hr, gprNumber_reg] at this
    rw [show (0x66 :: am.rexByte false dst :: 0x6B :: am.modrm (regLow dst) :: (am.tail ++ immBytes 8 imm)).length =
      5 + am.tail.length by simp; omega]
    exact this

theorem imul_r64_m64_imm8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) (imm : BitVec 8) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeImulR64M64Imm8 dst am imm).length)) 8)
      (codeRange p (r.prefixByte :: encodeImulR64M64Imm8 dst am imm))
      (Effect.post (imulR64M64Imm8SegEffect p (r.prefixByte :: encodeImulR64M64Imm8 dst am imm).length base
        (dst.setWidth 5) am imm)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := imul_r64_m64_imm8_seg_triple_of_bytes p r base _ hrex (regLow dst) am hv hx hb imm
  rw [hr, gprNumber_reg] at this
  unfold encodeImulR64M64Imm8
  rw [show (r.prefixByte :: am.rexByte true dst :: 0x6B :: am.modrm (regLow dst) ::
    (am.tail ++ immBytes 8 imm)).length = 5 + am.tail.length by simp; omega]
  exact this

theorem imul_r32_m32_imm8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) (imm : BitVec 8) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeImulR32M32Imm8 dst am imm).length)) 4)
      (codeRange p (r.prefixByte :: encodeImulR32M32Imm8 dst am imm))
      (Effect.post (imulR32M32Imm8SegEffect p (r.prefixByte :: encodeImulR32M32Imm8 dst am imm).length base
        (dst.setWidth 5) am imm)) := by
  unfold encodeImulR32M32Imm8
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := imul_r32_m32_imm8_seg_triple_of_bytes p r base (regLow dst) am hv hx hb imm
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    rw [show (r.prefixByte :: 0x6B :: am.modrm (regLow dst) :: (am.tail ++ immBytes 8 imm)).length =
      4 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := imul_r32_m32_imm8_rex_seg_triple_of_bytes p r base _ hrex (regLow dst) am hv hx hb imm
    rw [hr, gprNumber_reg] at this
    rw [show (r.prefixByte :: am.rexByte false dst :: 0x6B :: am.modrm (regLow dst) ::
      (am.tail ++ immBytes 8 imm)).length = 5 + am.tail.length by simp; omega]
    exact this

theorem imul_r16_m16_imm8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) (imm : BitVec 8) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeImulR16M16Imm8 dst am imm).length)) 2)
      (codeRange p (r.prefixByte :: encodeImulR16M16Imm8 dst am imm))
      (Effect.post (imulR16M16Imm8SegEffect p (r.prefixByte :: encodeImulR16M16Imm8 dst am imm).length base
        (dst.setWidth 5) am imm)) := by
  unfold encodeImulR16M16Imm8
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := imul_r16_m16_imm8_seg_triple_of_bytes p r base (regLow dst) am hv hx hb imm
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    rw [show (r.prefixByte :: 0x66 :: 0x6B :: am.modrm (regLow dst) :: (am.tail ++ immBytes 8 imm)).length =
      5 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := imul_r16_m16_imm8_rex_seg_triple_of_bytes p r base _ hrex (regLow dst) am hv hx hb imm
    rw [hr, gprNumber_reg] at this
    rw [show (r.prefixByte :: 0x66 :: am.rexByte false dst :: 0x6B :: am.modrm (regLow dst) ::
      (am.tail ++ immBytes 8 imm)).length = 6 + am.tail.length by simp; omega]
    exact this

theorem imul_r64_m64_imm8_a32_triple [Bindings] (p : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeImulR64M64Imm8 dst am imm).length)) 8)
      (codeRange p (0x67 :: encodeImulR64M64Imm8 dst am imm))
      (Effect.post (imulR64M64Imm8A32Effect p (0x67 :: encodeImulR64M64Imm8 dst am imm).length
        (dst.setWidth 5) am imm)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := imul_r64_m64_imm8_a32_triple_of_bytes p _ hrex (regLow dst) am hv hx hb imm
  rw [hr, gprNumber_reg] at this
  unfold encodeImulR64M64Imm8
  rw [show (0x67 :: am.rexByte true dst :: 0x6B :: am.modrm (regLow dst) ::
    (am.tail ++ immBytes 8 imm)).length = 5 + am.tail.length by simp; omega]
  exact this

theorem imul_r32_m32_imm8_a32_triple [Bindings] (p : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeImulR32M32Imm8 dst am imm).length)) 4)
      (codeRange p (0x67 :: encodeImulR32M32Imm8 dst am imm))
      (Effect.post (imulR32M32Imm8A32Effect p (0x67 :: encodeImulR32M32Imm8 dst am imm).length
        (dst.setWidth 5) am imm)) := by
  unfold encodeImulR32M32Imm8
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := imul_r32_m32_imm8_a32_triple_of_bytes p (regLow dst) am hv hx hb imm
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    rw [show (0x67 :: 0x6B :: am.modrm (regLow dst) :: (am.tail ++ immBytes 8 imm)).length =
      4 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := imul_r32_m32_imm8_rex_a32_triple_of_bytes p _ hrex (regLow dst) am hv hx hb imm
    rw [hr, gprNumber_reg] at this
    rw [show (0x67 :: am.rexByte false dst :: 0x6B :: am.modrm (regLow dst) ::
      (am.tail ++ immBytes 8 imm)).length = 5 + am.tail.length by simp; omega]
    exact this

theorem imul_r16_m16_imm8_a32_triple [Bindings] (p : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeImulR16M16Imm8 dst am imm).length)) 2)
      (codeRange p (0x67 :: encodeImulR16M16Imm8 dst am imm))
      (Effect.post (imulR16M16Imm8A32Effect p (0x67 :: encodeImulR16M16Imm8 dst am imm).length
        (dst.setWidth 5) am imm)) := by
  unfold encodeImulR16M16Imm8
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := imul_r16_m16_imm8_a32_triple_of_bytes p (regLow dst) am hv hx hb imm
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    rw [show (0x67 :: 0x66 :: 0x6B :: am.modrm (regLow dst) :: (am.tail ++ immBytes 8 imm)).length =
      5 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := imul_r16_m16_imm8_rex_a32_triple_of_bytes p _ hrex (regLow dst) am hv hx hb imm
    rw [hr, gprNumber_reg] at this
    rw [show (0x67 :: 0x66 :: am.rexByte false dst :: 0x6B :: am.modrm (regLow dst) ::
      (am.tail ++ immBytes 8 imm)).length = 6 + am.tail.length by simp; omega]
    exact this

attribute [x86_compose] imulR64M64Imm8Effect imulR32M32Imm8Effect imulR16M16Imm8Effect imulR64M64Imm8SegEffect imulR32M32Imm8SegEffect imulR16M16Imm8SegEffect imulR64M64Imm8A32Effect imulR32M32Imm8A32Effect imulR16M16Imm8A32Effect

@[x86_local] theorem imulR64M64Imm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (imulR64M64Imm8Effect p len dst am imm) := by
  effect_local [imulR64M64Imm8Effect, imulFlags]

@[x86_local] theorem imulR64M64Imm8SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (imulR64M64Imm8SegEffect p len base dst am imm) := by
  effect_local [imulR64M64Imm8SegEffect, imulFlags]

@[x86_local] theorem imulR64M64Imm8A32Effect_local {p : BitVec 64} {len : Nat}
    {dst : BitVec 5} {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (imulR64M64Imm8A32Effect p len dst am imm) := by
  effect_local [imulR64M64Imm8A32Effect, imulFlags]

@[x86_local] theorem imulR32M32Imm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (imulR32M32Imm8Effect p len dst am imm) := by
  effect_local [imulR32M32Imm8Effect, imulFlags]

@[x86_local] theorem imulR32M32Imm8SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (imulR32M32Imm8SegEffect p len base dst am imm) := by
  effect_local [imulR32M32Imm8SegEffect, imulFlags]

@[x86_local] theorem imulR32M32Imm8A32Effect_local {p : BitVec 64} {len : Nat}
    {dst : BitVec 5} {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (imulR32M32Imm8A32Effect p len dst am imm) := by
  effect_local [imulR32M32Imm8A32Effect, imulFlags]

@[x86_local] theorem imulR16M16Imm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (imulR16M16Imm8Effect p len dst am imm) := by
  effect_local [imulR16M16Imm8Effect, imulFlags]

@[x86_local] theorem imulR16M16Imm8SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (imulR16M16Imm8SegEffect p len base dst am imm) := by
  effect_local [imulR16M16Imm8SegEffect, imulFlags]

@[x86_local] theorem imulR16M16Imm8A32Effect_local {p : BitVec 64} {len : Nat}
    {dst : BitVec 5} {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (imulR16M16Imm8A32Effect p len dst am imm) := by
  effect_local [imulR16M16Imm8A32Effect, imulFlags]

end X86Proofs
