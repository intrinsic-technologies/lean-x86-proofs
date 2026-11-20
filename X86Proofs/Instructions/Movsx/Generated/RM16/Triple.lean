import X86Proofs.Instructions.Movsx.Generated.RM16.Step
import X86Proofs.Instructions.Movsx.Generated.RM16.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movsxR64M16Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let x := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      (x).signExtend 64⟩] }

@[simp] theorem movsxR64M16Effect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (movsxR64M16Effect p len dst am s).components = [.reg dst, .rip] := rfl

def movsxR64M16SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let x := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      (x).signExtend 64⟩] }

@[simp] theorem movsxR64M16SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (movsxR64M16SegEffect p len base dst am s).components = [.reg dst, .rip] := rfl

def movsxR64M16A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    Effect :=
  let x := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      (x).signExtend 64⟩] }

@[simp] theorem movsxR64M16A32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : (movsxR64M16A32Effect p len dst am s).components = [.reg dst, .rip] := rfl

def movsxR32M16Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let x := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      ((x).signExtend 32).setWidth 64⟩] }

@[simp] theorem movsxR32M16Effect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (movsxR32M16Effect p len dst am s).components = [.reg dst, .rip] := rfl

def movsxR32M16SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let x := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      ((x).signExtend 32).setWidth 64⟩] }

@[simp] theorem movsxR32M16SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (movsxR32M16SegEffect p len base dst am s).components = [.reg dst, .rip] := rfl

def movsxR32M16A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    Effect :=
  let x := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      ((x).signExtend 32).setWidth 64⟩] }

@[simp] theorem movsxR32M16A32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : (movsxR32M16A32Effect p len dst am s).components = [.reg dst, .rip] := rfl

def movsxR16M16Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let x := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 ((x).signExtend 16) ((Operand.reg dst : Operand 64).read s)⟩] }

@[simp] theorem movsxR16M16Effect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (movsxR16M16Effect p len dst am s).components = [.reg dst, .rip] := rfl

def movsxR16M16SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let x := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 ((x).signExtend 16) ((Operand.reg dst : Operand 64).read s)⟩] }

@[simp] theorem movsxR16M16SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (movsxR16M16SegEffect p len base dst am s).components = [.reg dst, .rip] := rfl

def movsxR16M16A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    Effect :=
  let x := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 ((x).signExtend 16) ((Operand.reg dst : Operand 64).read s)⟩] }

@[simp] theorem movsxR16M16A32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : (movsxR16M16A32Effect p len dst am s).components = [.reg dst, .rip] := rfl

theorem movsx_r64_m16_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (rex :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (movsxR64M16Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := movsx_r64_m16_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp)
    (by rw [scanContext_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, movsxSpec]
  rfl

theorem movsx_r64_m16_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (rex :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (Effect.post (movsxR64M16Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxR64M16Effect_components]; simp [Component.Covers]) _)
    (movsx_r64_m16_effect_step p rex hrex reg am hv hx hb)

theorem movsx_r32_m16_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 2)
      (codeRange p (0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (movsxR32M16Effect p (3 + am.tail.length) (gprNumber 0 0 reg)
        am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := movsx_r32_m16_step s h [] (by simp)
    (by simp)
    (by rfl)
    (by rfl)
    (by rfl) (by rfl)
    (by rfl) reg am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movsxSpec]
  rfl

theorem movsx_r32_m16_triple_of_bytes [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 2)
      (codeRange p (0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (Effect.post (movsxR32M16Effect p (3 + am.tail.length) (gprNumber 0 0 reg)
        am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxR32M16Effect_components]; simp [Component.Covers]) _)
    (movsx_r32_m16_effect_step p reg am hv hx hb)

theorem movsx_r32_m16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (rex :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (movsxR32M16Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := movsx_r32_m16_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movsxSpec]
  rfl

theorem movsx_r32_m16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (rex :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (Effect.post (movsxR32M16Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxR32M16Effect_components]; simp [Component.Covers]) _)
    (movsx_r32_m16_rex_effect_step p rex hrex reg am hv hx hb)

theorem movsx_r16_m16_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (0x66 :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (movsxR16M16Effect p (4 + am.tail.length) (gprNumber 0 0 reg)
        am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := movsx_r16_m16_step s h [0x66] (by simpa using scanPrefix_66)
    (by simp)
    (by rfl)
    (by rfl)
    (by rfl) (by rfl)
    (by rfl) reg am hv
    (by exact (AddrContext.osz _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, Operand.read_reg_dataAccess, movsxSpec]
  rfl

theorem movsx_r16_m16_triple_of_bytes [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (0x66 :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (Effect.post (movsxR16M16Effect p (4 + am.tail.length) (gprNumber 0 0 reg)
        am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxR16M16Effect_components]; simp [Component.Covers]) _)
    (movsx_r16_m16_effect_step p reg am hv hx hb)

theorem movsx_r16_m16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (0x66 :: rex :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (movsxR16M16Effect p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := movsx_r16_m16_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix])
    (by simp)
    (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_66_rex _ _ hr]; exact (AddrContext.oszRex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_66_rex _ _ hr]; exact hread)
  simp only [scanContext_66_rex _ _ hr] at hstep
  have hdst : gprNumber (oszRexContext s.DS rex.toBitVec).rex_r4
      (oszRexContext s.DS rex.toBitVec).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, Operand.read_reg_dataAccess, movsxSpec]
  rfl

theorem movsx_r16_m16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (0x66 :: rex :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (Effect.post (movsxR16M16Effect p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxR16M16Effect_components]; simp [Component.Covers]) _)
    (movsx_r16_m16_rex_effect_step p rex hrex reg am hv hx hb)

theorem movsx_r64_m16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (movsxR64M16SegEffect p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg)
        am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := movsx_r64_m16_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix))
    (by simp)
    (by rw [hsc]; exact hrex.rex_w s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, movsxSpec]
  rfl

theorem movsx_r64_m16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (Effect.post (movsxR64M16SegEffect p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxR64M16SegEffect_components]; simp [Component.Covers]) _)
    (movsx_r64_m16_seg_effect_step p r base rex hrex reg am hv hx hb)

theorem movsx_r32_m16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (movsxR32M16SegEffect p (4 + am.tail.length) base (gprNumber 0 0 reg)
        am) := by
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := movsx_r32_m16_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp))
    (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movsxSpec]
  rfl

theorem movsx_r32_m16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (Effect.post (movsxR32M16SegEffect p (4 + am.tail.length) base (gprNumber 0 0 reg)
        am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxR32M16SegEffect_components]; simp [Component.Covers]) _)
    (movsx_r32_m16_seg_effect_step p r base reg am hv hx hb)

theorem movsx_r32_m16_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (movsxR32M16SegEffect p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg)
        am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := movsx_r32_m16_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix))
    (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hrex.rex_w s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movsxSpec]
  rfl

theorem movsx_r32_m16_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (Effect.post (movsxR32M16SegEffect p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxR32M16SegEffect_components]; simp [Component.Covers]) _)
    (movsx_r32_m16_rex_seg_effect_step p r base rex hrex reg am hv hx hb)

theorem movsx_r16_m16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (movsxR16M16SegEffect p (5 + am.tail.length) base (gprNumber 0 0 reg)
        am) := by
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66]
      (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil)]
  have hstep := movsx_r16_m16_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66))
    (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, Operand.read_reg_dataAccess, movsxSpec]
  rfl

theorem movsx_r16_m16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (Effect.post (movsxR16M16SegEffect p (5 + am.tail.length) base (gprNumber 0 0 reg)
        am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxR16M16SegEffect_components]; simp [Component.Covers]) _)
    (movsx_r16_m16_seg_effect_step p r base reg am hv hx hb)

theorem movsx_r16_m16_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (movsxR16M16SegEffect p (6 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg)
        am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66, rex] =
      withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66, rex]
      (noSegPrefix_cons noSegPrefix_66 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_66_rex _ _ hr]
  have hstep := movsx_r16_m16_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix]))
    (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hrex.rex_w s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hdst : gprNumber (withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, Operand.read_reg_dataAccess, movsxSpec]
  rfl

theorem movsx_r16_m16_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (Effect.post (movsxR16M16SegEffect p (6 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxR16M16SegEffect_components]; simp [Component.Covers]) _)
    (movsx_r16_m16_rex_seg_effect_step p r base rex hrex reg am hv hx hb)

theorem movsx_r64_m16_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (movsxR64M16A32Effect p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := movsx_r64_m16_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix))
    (by simp)
    (by rw [hsc]; exact hrex.rex_w s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (rexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (rexContext s.DS rex.toBitVec)).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, movsxSpec]
  rfl

theorem movsx_r64_m16_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (Effect.post (movsxR64M16A32Effect p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxR64M16A32Effect_components]; simp [Component.Covers]) _)
    (movsx_r64_m16_a32_effect_step p rex hrex reg am hv hx hb)

theorem movsx_r32_m16_a32_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (movsxR32M16A32Effect p (4 + am.tail.length) (gprNumber 0 0 reg)
        am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := movsx_r32_m16_a32_step s h [0x67] (scanPrefix_asz_cons (by simp))
    (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r4
      (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movsxSpec]
  rfl

theorem movsx_r32_m16_a32_triple_of_bytes [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (Effect.post (movsxR32M16A32Effect p (4 + am.tail.length) (gprNumber 0 0 reg)
        am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxR32M16A32Effect_components]; simp [Component.Covers]) _)
    (movsx_r32_m16_a32_effect_step p reg am hv hx hb)

theorem movsx_r32_m16_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (movsxR32M16A32Effect p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := movsx_r32_m16_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix))
    (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hrex.rex_w s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (rexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (rexContext s.DS rex.toBitVec)).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movsxSpec]
  rfl

theorem movsx_r32_m16_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (Effect.post (movsxR32M16A32Effect p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxR32M16A32Effect_components]; simp [Component.Covers]) _)
    (movsx_r32_m16_rex_a32_effect_step p rex hrex reg am hv hx hb)

theorem movsx_r16_m16_a32_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (movsxR16M16A32Effect p (5 + am.tail.length) (gprNumber 0 0 reg)
        am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66]) := by
    rw [scanContext_asz_cons]
  have hstep := movsx_r16_m16_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66))
    (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66])).rex_r4
      (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66])).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, Operand.read_reg_dataAccess, movsxSpec]
  rfl

theorem movsx_r16_m16_a32_triple_of_bytes [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (Effect.post (movsxR16M16A32Effect p (5 + am.tail.length) (gprNumber 0 0 reg)
        am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxR16M16A32Effect_components]; simp [Component.Covers]) _)
    (movsx_r16_m16_a32_effect_step p reg am hv hx hb)

theorem movsx_r16_m16_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (movsxR16M16A32Effect p (6 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66, rex] =
      withAsz (oszRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_66_rex _ _ hr]
  have hstep := movsx_r16_m16_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix]))
    (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hrex.rex_w s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (oszRexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (oszRexContext s.DS rex.toBitVec)).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, Operand.read_reg_dataAccess, movsxSpec]
  rfl

theorem movsx_r16_m16_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x0F :: 0xBF :: am.modrm reg :: am.tail))
      (Effect.post (movsxR16M16A32Effect p (6 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxR16M16A32Effect_components]; simp [Component.Covers]) _)
    (movsx_r16_m16_rex_a32_effect_step p rex hrex reg am hv hx hb)

theorem movsx_r64_m16_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (LoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeMovsxR64M16 dst am).length)) 2)
      (codeRange p (encodeMovsxR64M16 dst am))
      (Effect.post
        (movsxR64M16Effect p (encodeMovsxR64M16 dst am).length (dst.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := movsx_r64_m16_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
  rw [hr, gprNumber_reg] at this
  unfold encodeMovsxR64M16
  rw [show (am.rexByte true dst :: 0x0F :: 0xBF :: am.modrm (regLow dst) :: am.tail).length =
    4 + am.tail.length by simp; omega]
  exact this

theorem movsx_r32_m16_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (LoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeMovsxR32M16 dst am).length)) 2)
      (codeRange p (encodeMovsxR32M16 dst am))
      (Effect.post
        (movsxR32M16Effect p (encodeMovsxR32M16 dst am).length (dst.setWidth 5) am)) := by
  unfold encodeMovsxR32M16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := movsx_r32_m16_triple_of_bytes p (regLow dst) am hv hx hb
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    rw [show (0x0F :: 0xBF :: am.modrm (regLow dst) :: am.tail).length =
      3 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := movsx_r32_m16_rex_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    rw [show (am.rexByte false dst :: 0x0F :: 0xBF :: am.modrm (regLow dst) ::
      am.tail).length = 4 + am.tail.length by simp; omega]
    exact this

theorem movsx_r16_m16_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (LoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeMovsxR16M16 dst am).length)) 2)
      (codeRange p (encodeMovsxR16M16 dst am))
      (Effect.post
        (movsxR16M16Effect p (encodeMovsxR16M16 dst am).length (dst.setWidth 5) am)) := by
  unfold encodeMovsxR16M16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := movsx_r16_m16_triple_of_bytes p (regLow dst) am hv hx hb
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    rw [show (0x66 :: 0x0F :: 0xBF :: am.modrm (regLow dst) :: am.tail).length =
      4 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := movsx_r16_m16_rex_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    rw [show (0x66 :: am.rexByte false dst :: 0x0F :: 0xBF :: am.modrm (regLow dst) ::
      am.tail).length = 5 + am.tail.length by simp; omega]
    exact this

theorem movsx_r64_m16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (SegLoadPre p r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeMovsxR64M16 dst am).length)) 2)
      (codeRange p (r.prefixByte :: encodeMovsxR64M16 dst am))
      (Effect.post
        (movsxR64M16SegEffect p (r.prefixByte :: encodeMovsxR64M16 dst am).length base (dst.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := movsx_r64_m16_seg_triple_of_bytes p r base _ hrex (regLow dst) am hv hx hb
  rw [hr, gprNumber_reg] at this
  unfold encodeMovsxR64M16
  rw [show (r.prefixByte :: am.rexByte true dst :: 0x0F :: 0xBF :: am.modrm (regLow dst) ::
    am.tail).length = 5 + am.tail.length by simp; omega]
  exact this

theorem movsx_r32_m16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (SegLoadPre p r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeMovsxR32M16 dst am).length)) 2)
      (codeRange p (r.prefixByte :: encodeMovsxR32M16 dst am))
      (Effect.post
        (movsxR32M16SegEffect p (r.prefixByte :: encodeMovsxR32M16 dst am).length base (dst.setWidth 5) am)) := by
  unfold encodeMovsxR32M16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := movsx_r32_m16_seg_triple_of_bytes p r base (regLow dst) am hv hx hb
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    rw [show (r.prefixByte :: 0x0F :: 0xBF :: am.modrm (regLow dst) :: am.tail).length =
      4 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := movsx_r32_m16_rex_seg_triple_of_bytes p r base _ hrex (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    rw [show (r.prefixByte :: am.rexByte false dst :: 0x0F :: 0xBF ::
      am.modrm (regLow dst) :: am.tail).length = 5 + am.tail.length by simp; omega]
    exact this

theorem movsx_r16_m16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (SegLoadPre p r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeMovsxR16M16 dst am).length)) 2)
      (codeRange p (r.prefixByte :: encodeMovsxR16M16 dst am))
      (Effect.post
        (movsxR16M16SegEffect p (r.prefixByte :: encodeMovsxR16M16 dst am).length base (dst.setWidth 5) am)) := by
  unfold encodeMovsxR16M16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := movsx_r16_m16_seg_triple_of_bytes p r base (regLow dst) am hv hx hb
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    rw [show (r.prefixByte :: 0x66 :: 0x0F :: 0xBF :: am.modrm (regLow dst) :: am.tail).length =
      5 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := movsx_r16_m16_rex_seg_triple_of_bytes p r base _ hrex (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    rw [show (r.prefixByte :: 0x66 :: am.rexByte false dst :: 0x0F :: 0xBF ::
      am.modrm (regLow dst) :: am.tail).length = 6 + am.tail.length by simp; omega]
    exact this

theorem movsx_r64_m16_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (LoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeMovsxR64M16 dst am).length)) 2)
      (codeRange p (0x67 :: encodeMovsxR64M16 dst am))
      (Effect.post
        (movsxR64M16A32Effect p (0x67 :: encodeMovsxR64M16 dst am).length (dst.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := movsx_r64_m16_a32_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
  rw [hr, gprNumber_reg] at this
  unfold encodeMovsxR64M16
  rw [show (0x67 :: am.rexByte true dst :: 0x0F :: 0xBF :: am.modrm (regLow dst) ::
    am.tail).length = 5 + am.tail.length by simp; omega]
  exact this

theorem movsx_r32_m16_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (LoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeMovsxR32M16 dst am).length)) 2)
      (codeRange p (0x67 :: encodeMovsxR32M16 dst am))
      (Effect.post
        (movsxR32M16A32Effect p (0x67 :: encodeMovsxR32M16 dst am).length (dst.setWidth 5) am)) := by
  unfold encodeMovsxR32M16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := movsx_r32_m16_a32_triple_of_bytes p (regLow dst) am hv hx hb
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    rw [show (0x67 :: 0x0F :: 0xBF :: am.modrm (regLow dst) :: am.tail).length =
      4 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := movsx_r32_m16_rex_a32_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    rw [show (0x67 :: am.rexByte false dst :: 0x0F :: 0xBF ::
      am.modrm (regLow dst) :: am.tail).length = 5 + am.tail.length by simp; omega]
    exact this

theorem movsx_r16_m16_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (LoadPre p
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeMovsxR16M16 dst am).length)) 2)
      (codeRange p (0x67 :: encodeMovsxR16M16 dst am))
      (Effect.post
        (movsxR16M16A32Effect p (0x67 :: encodeMovsxR16M16 dst am).length (dst.setWidth 5) am)) := by
  unfold encodeMovsxR16M16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := movsx_r16_m16_a32_triple_of_bytes p (regLow dst) am hv hx hb
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    rw [show (0x67 :: 0x66 :: 0x0F :: 0xBF :: am.modrm (regLow dst) :: am.tail).length =
      5 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := movsx_r16_m16_rex_a32_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    rw [show (0x67 :: 0x66 :: am.rexByte false dst :: 0x0F :: 0xBF ::
      am.modrm (regLow dst) :: am.tail).length = 6 + am.tail.length by simp; omega]
    exact this

attribute [x86_compose] movsxR64M16Effect movsxR32M16Effect movsxR16M16Effect movsxR64M16SegEffect movsxR32M16SegEffect movsxR16M16SegEffect movsxR64M16A32Effect movsxR32M16A32Effect movsxR16M16A32Effect

@[x86_local] theorem movsxR64M16Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (movsxR64M16Effect p len dst am) := by
  effect_local [movsxR64M16Effect]

@[x86_local] theorem movsxR64M16SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} :
    Effect.Local (movsxR64M16SegEffect p len base dst am) := by
  effect_local [movsxR64M16SegEffect]

@[x86_local] theorem movsxR64M16A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (movsxR64M16A32Effect p len dst am) := by
  effect_local [movsxR64M16A32Effect]

@[x86_local] theorem movsxR32M16Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (movsxR32M16Effect p len dst am) := by
  effect_local [movsxR32M16Effect]

@[x86_local] theorem movsxR32M16SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} :
    Effect.Local (movsxR32M16SegEffect p len base dst am) := by
  effect_local [movsxR32M16SegEffect]

@[x86_local] theorem movsxR32M16A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (movsxR32M16A32Effect p len dst am) := by
  effect_local [movsxR32M16A32Effect]

@[x86_local] theorem movsxR16M16Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (movsxR16M16Effect p len dst am) := by
  effect_local [movsxR16M16Effect]

@[x86_local] theorem movsxR16M16SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} :
    Effect.Local (movsxR16M16SegEffect p len base dst am) := by
  effect_local [movsxR16M16SegEffect]

@[x86_local] theorem movsxR16M16A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (movsxR16M16A32Effect p len dst am) := by
  effect_local [movsxR16M16A32Effect]

end X86Proofs
