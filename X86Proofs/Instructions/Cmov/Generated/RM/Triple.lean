import X86Proofs.Instructions.Cmov.Generated.RM.Step
import X86Proofs.Instructions.Cmov.Generated.RM.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cmovR64M64Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (c : Bool) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), if c then b else a⟩]
    flags := none }

@[simp] theorem cmovR64M64Effect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (am : AddrMode) (c : Bool) (s : RamState) :
    (cmovR64M64Effect p len dst am c s).components = [.reg dst, .rip] := rfl

def cmovR64M64SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (c : Bool) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), if c then b else a⟩]
    flags := none }

@[simp] theorem cmovR64M64SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (c : Bool) (s : RamState) :
    (cmovR64M64SegEffect p len base dst am c s).components = [.reg dst, .rip] := rfl

def cmovR64M64A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), if c then b else a⟩]
    flags := none }

@[simp] theorem cmovR64M64A32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (c : Bool) (s : RamState) :
    (cmovR64M64A32Effect p len dst am c s).components = [.reg dst, .rip] := rfl

def cmovR32M32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (c : Bool) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (if c then b else a).setWidth 64⟩]
    flags := none }

@[simp] theorem cmovR32M32Effect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (am : AddrMode) (c : Bool) (s : RamState) :
    (cmovR32M32Effect p len dst am c s).components = [.reg dst, .rip] := rfl

def cmovR32M32SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (c : Bool) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (if c then b else a).setWidth 64⟩]
    flags := none }

@[simp] theorem cmovR32M32SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (c : Bool) (s : RamState) :
    (cmovR32M32SegEffect p len base dst am c s).components = [.reg dst, .rip] := rfl

def cmovR32M32A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), (if c then b else a).setWidth 64⟩]
    flags := none }

@[simp] theorem cmovR32M32A32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (c : Bool) (s : RamState) :
    (cmovR32M32A32Effect p len dst am c s).components = [.reg dst, .rip] := rfl

def cmovR16M16Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (c : Bool) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (if c then b else a) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := none }

@[simp] theorem cmovR16M16Effect_components (p : BitVec 64) (len : Nat)
    (dst : BitVec 5) (am : AddrMode) (c : Bool) (s : RamState) :
    (cmovR16M16Effect p len dst am c s).components = [.reg dst, .rip] := rfl

def cmovR16M16SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (c : Bool) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (if c then b else a) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := none }

@[simp] theorem cmovR16M16SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (c : Bool) (s : RamState) :
    (cmovR16M16SegEffect p len base dst am c s).components = [.reg dst, .rip] := rfl

def cmovR16M16A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (c : Bool)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (if c then b else a) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := none }

@[simp] theorem cmovR16M16A32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (c : Bool) (s : RamState) :
    (cmovR16M16A32Effect p len dst am c s).components = [.reg dst, .rip] := rfl

theorem cmov_r64_m64_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s =>
        LoadPre p
          (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (rex :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (cmovR64M64Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, hread⟩, hc⟩
  subst hp hc
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := cmov_r_m_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) cc reg am hv
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
  simp only [Operand.read_writeResult_self, cmovSpec]
  rfl

theorem cmov_r64_m64_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s =>
        LoadPre p
          (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (rex :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (Effect.post
        (cmovR64M64Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmovR64M64Effect_components]; simp [Component.Covers]) _)
    (cmov_r64_m64_effect_step p cc rex hrex reg am hv hx hb c)

theorem cmov_r32_m32_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s =>
        LoadPre p
          (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (cmovR32M32Effect p (3 + am.tail.length) (gprNumber 0 0 reg) am c) := by
  rintro s h hcode ⟨⟨hp, hread⟩, hc⟩
  subst hp hc
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := cmov_r_m_step s h [] (by simp) (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) cc reg am hv
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
  simp only [Operand.read_writeResult_self32, cmovSpec]
  rfl

theorem cmov_r32_m32_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s =>
        LoadPre p
          (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (Effect.post
        (cmovR32M32Effect p (3 + am.tail.length) (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmovR32M32Effect_components]; simp [Component.Covers]) _)
    (cmov_r32_m32_effect_step p cc reg am hv hx hb c)

theorem cmov_r32_m32_rex_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s =>
        LoadPre p
          (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (rex :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (cmovR32M32Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, hread⟩, hc⟩
  subst hp hc
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := cmov_r_m_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) cc reg am hv
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
  simp only [Operand.read_writeResult_self32, cmovSpec]
  rfl

theorem cmov_r32_m32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s =>
        LoadPre p
          (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (rex :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (Effect.post
        (cmovR32M32Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmovR32M32Effect_components]; simp [Component.Covers]) _)
    (cmov_r32_m32_rex_effect_step p cc rex hrex reg am hv hx hb c)

theorem cmov_r16_m16_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s =>
        LoadPre p
          (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x66 :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (cmovR16M16Effect p (4 + am.tail.length) (gprNumber 0 0 reg) am c) := by
  rintro s h hcode ⟨⟨hp, hread⟩, hc⟩
  subst hp hc
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := cmov_r16_m16_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) cc reg am hv
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
    Operand.read_beforeFetch, Operand.read_reg_dataAccess, cmovSpec]
  rfl

theorem cmov_r16_m16_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s =>
        LoadPre p
          (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x66 :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (Effect.post
        (cmovR16M16Effect p (4 + am.tail.length) (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmovR16M16Effect_components]; simp [Component.Covers]) _)
    (cmov_r16_m16_effect_step p cc reg am hv hx hb c)

theorem cmov_r16_m16_rex_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s =>
        LoadPre p
          (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x66 :: rex :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (cmovR16M16Effect p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, hread⟩, hc⟩
  subst hp hc
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := cmov_r16_m16_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; rfl) cc reg am hv
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
    Operand.read_beforeFetch, Operand.read_reg_dataAccess, cmovSpec]
  rfl

theorem cmov_r16_m16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s =>
        LoadPre p
          (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x66 :: rex :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (Effect.post
        (cmovR16M16Effect p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmovR16M16Effect_components]; simp [Component.Covers]) _)
    (cmov_r16_m16_rex_effect_step p cc rex hrex reg am hv hx hb c)

theorem cmov_r64_m64_seg_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s =>
        SegLoadPre p r base
          (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (cmovR64M64SegEffect p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, ⟨hseg, hbase⟩, hread⟩, hc⟩
  subst hp hc hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := cmov_r_m_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) cc reg am hv
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
  simp only [Operand.read_writeResult_self, cmovSpec]
  rfl

theorem cmov_r64_m64_seg_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s =>
        SegLoadPre p r base
          (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (Effect.post
        (cmovR64M64SegEffect p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmovR64M64SegEffect_components]; simp [Component.Covers]) _)
    (cmov_r64_m64_seg_effect_step p cc r base rex hrex reg am hv hx hb c)

theorem cmov_r32_m32_seg_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (r : SegReg)
    (base : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s =>
        SegLoadPre p r base
          (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (r.prefixByte :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (cmovR32M32SegEffect p (4 + am.tail.length) base (gprNumber 0 0 reg) am c) := by
  rintro s h hcode ⟨⟨hp, ⟨hseg, hbase⟩, hread⟩, hc⟩
  subst hp hc hbase
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := cmov_r_m_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) cc reg am hv
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
  simp only [Operand.read_writeResult_self32, cmovSpec]
  rfl

theorem cmov_r32_m32_seg_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (r : SegReg)
    (base : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s =>
        SegLoadPre p r base
          (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (r.prefixByte :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (Effect.post
        (cmovR32M32SegEffect p (4 + am.tail.length) base (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmovR32M32SegEffect_components]; simp [Component.Covers]) _)
    (cmov_r32_m32_seg_effect_step p cc r base reg am hv hx hb c)

theorem cmov_r32_m32_rex_seg_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s =>
        SegLoadPre p r base
          (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (cmovR32M32SegEffect p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, ⟨hseg, hbase⟩, hread⟩, hc⟩
  subst hp hc hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := cmov_r_m_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) cc reg am hv
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
  simp only [Operand.read_writeResult_self32, cmovSpec]
  rfl

theorem cmov_r32_m32_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s =>
        SegLoadPre p r base
          (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (Effect.post
        (cmovR32M32SegEffect p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmovR32M32SegEffect_components]; simp [Component.Covers]) _)
    (cmov_r32_m32_rex_seg_effect_step p cc r base rex hrex reg am hv hx hb c)

theorem cmov_r16_m16_seg_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (r : SegReg)
    (base : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s =>
        SegLoadPre p r base
          (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (r.prefixByte :: 0x66 :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (cmovR16M16SegEffect p (5 + am.tail.length) base (gprNumber 0 0 reg) am c) := by
  rintro s h hcode ⟨⟨hp, ⟨hseg, hbase⟩, hread⟩, hc⟩
  subst hp hc hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66]
      (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil)]
  have hstep := cmov_r16_m16_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) cc reg am hv
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
    Operand.read_beforeFetch, Operand.read_reg_dataAccess, cmovSpec]
  rfl

theorem cmov_r16_m16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (r : SegReg)
    (base : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s =>
        SegLoadPre p r base
          (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (r.prefixByte :: 0x66 :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (Effect.post
        (cmovR16M16SegEffect p (5 + am.tail.length) base (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmovR16M16SegEffect_components]; simp [Component.Covers]) _)
    (cmov_r16_m16_seg_effect_step p cc r base reg am hv hx hb c)

theorem cmov_r16_m16_rex_seg_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s =>
        SegLoadPre p r base
          (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (cmovR16M16SegEffect p (6 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, ⟨hseg, hbase⟩, hread⟩, hc⟩
  subst hp hc hbase
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66, rex] =
      withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66, rex]
      (noSegPrefix_cons noSegPrefix_66 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_66_rex _ _ hr]
  have hstep := cmov_r16_m16_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) cc reg am hv
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
    Operand.read_beforeFetch, Operand.read_reg_dataAccess, cmovSpec]
  rfl

theorem cmov_r16_m16_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s =>
        SegLoadPre p r base
          (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (Effect.post
        (cmovR16M16SegEffect p (6 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmovR16M16SegEffect_components]; simp [Component.Covers]) _)
    (cmov_r16_m16_rex_seg_effect_step p cc r base rex hrex reg am hv hx hb c)

theorem cmov_r64_m64_a32_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s =>
        LoadPre p
          (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x67 :: rex :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (cmovR64M64A32Effect p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, hread⟩, hc⟩
  subst hp hc
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := cmov_r_m_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) cc reg am hv
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
  simp only [Operand.read_writeResult_self, cmovSpec]
  rfl

theorem cmov_r64_m64_a32_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s =>
        LoadPre p
          (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x67 :: rex :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (Effect.post
        (cmovR64M64A32Effect p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmovR64M64A32Effect_components]; simp [Component.Covers]) _)
    (cmov_r64_m64_a32_effect_step p cc rex hrex reg am hv hx hb c)

theorem cmov_r32_m32_a32_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s =>
        LoadPre p
          (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x67 :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (cmovR32M32A32Effect p (4 + am.tail.length) (gprNumber 0 0 reg) am c) := by
  rintro s h hcode ⟨⟨hp, hread⟩, hc⟩
  subst hp hc
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := cmov_r_m_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) cc reg am hv
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
  simp only [Operand.read_writeResult_self32, cmovSpec]
  rfl

theorem cmov_r32_m32_a32_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s =>
        LoadPre p
          (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x67 :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (Effect.post
        (cmovR32M32A32Effect p (4 + am.tail.length) (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmovR32M32A32Effect_components]; simp [Component.Covers]) _)
    (cmov_r32_m32_a32_effect_step p cc reg am hv hx hb c)

theorem cmov_r32_m32_rex_a32_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s =>
        LoadPre p
          (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x67 :: rex :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (cmovR32M32A32Effect p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, hread⟩, hc⟩
  subst hp hc
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := cmov_r_m_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) cc reg am hv
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
  simp only [Operand.read_writeResult_self32, cmovSpec]
  rfl

theorem cmov_r32_m32_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s =>
        LoadPre p
          (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x67 :: rex :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (Effect.post
        (cmovR32M32A32Effect p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmovR32M32A32Effect_components]; simp [Component.Covers]) _)
    (cmov_r32_m32_rex_a32_effect_step p cc rex hrex reg am hv hx hb c)

theorem cmov_r16_m16_a32_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s =>
        LoadPre p
          (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x67 :: 0x66 :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (cmovR16M16A32Effect p (5 + am.tail.length) (gprNumber 0 0 reg) am c) := by
  rintro s h hcode ⟨⟨hp, hread⟩, hc⟩
  subst hp hc
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66]) := by
    rw [scanContext_asz_cons]
  have hstep := cmov_r16_m16_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) cc reg am hv
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
    Operand.read_beforeFetch, Operand.read_reg_dataAccess, cmovSpec]
  rfl

theorem cmov_r16_m16_a32_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s =>
        LoadPre p
          (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x67 :: 0x66 :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (Effect.post
        (cmovR16M16A32Effect p (5 + am.tail.length) (gprNumber 0 0 reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmovR16M16A32Effect_components]; simp [Component.Covers]) _)
    (cmov_r16_m16_a32_effect_step p cc reg am hv hx hb c)

theorem cmov_r16_m16_rex_a32_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s =>
        LoadPre p
          (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (cmovR16M16A32Effect p (6 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, hread⟩, hc⟩
  subst hp hc
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66, rex] =
      withAsz (oszRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_66_rex _ _ hr]
  have hstep := cmov_r16_m16_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) cc reg am hv
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
    Operand.read_beforeFetch, Operand.read_reg_dataAccess, cmovSpec]
  rfl

theorem cmov_r16_m16_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s =>
        LoadPre p
          (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x0F :: cmovOpcode cc :: am.modrm reg :: am.tail))
      (Effect.post
        (cmovR16M16A32Effect p (6 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmovR16M16A32Effect_components]; simp [Component.Covers]) _)
    (cmov_r16_m16_rex_a32_effect_step p cc rex hrex reg am hv hx hb c)

theorem cmov_r64_m64_triple [Bindings] (p : BitVec 64) (cc : BitVec 4) (dst : BitVec 4)
    (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s =>
        LoadPre p
          (fun s => am.addr s (p + BitVec.ofNat 64 (encodeCmovR64M64 cc dst am).length)) 8 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (encodeCmovR64M64 cc dst am))
      (Effect.post
        (cmovR64M64Effect p (encodeCmovR64M64 cc dst am).length (dst.setWidth 5) am c)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := cmov_r64_m64_triple_of_bytes p cc _ hrex (regLow dst) am hv hx hb c
  rw [hr, gprNumber_reg] at this
  unfold encodeCmovR64M64
  rw [show (am.rexByte true dst :: 0x0F :: cmovOpcode cc :: am.modrm (regLow dst) ::
    am.tail).length = 4 + am.tail.length by simp; omega]
  exact this

theorem cmov_r32_m32_triple [Bindings] (p : BitVec 64) (cc : BitVec 4) (dst : BitVec 4)
    (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s =>
        LoadPre p
          (fun s => am.addr s (p + BitVec.ofNat 64 (encodeCmovR32M32 cc dst am).length)) 4 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (encodeCmovR32M32 cc dst am))
      (Effect.post
        (cmovR32M32Effect p (encodeCmovR32M32 cc dst am).length (dst.setWidth 5) am c)) := by
  unfold encodeCmovR32M32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := cmov_r32_m32_triple_of_bytes p cc (regLow dst) am hv hx hb c
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    rw [show (0x0F :: cmovOpcode cc :: am.modrm (regLow dst) :: am.tail).length =
      3 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := cmov_r32_m32_rex_triple_of_bytes p cc _ hrex (regLow dst) am hv hx hb c
    rw [hr, gprNumber_reg] at this
    rw [show (am.rexByte false dst :: 0x0F :: cmovOpcode cc :: am.modrm (regLow dst) ::
      am.tail).length = 4 + am.tail.length by simp; omega]
    exact this

theorem cmov_r16_m16_triple [Bindings] (p : BitVec 64) (cc : BitVec 4) (dst : BitVec 4)
    (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s =>
        LoadPre p
          (fun s => am.addr s (p + BitVec.ofNat 64 (encodeCmovR16M16 cc dst am).length)) 2 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (encodeCmovR16M16 cc dst am))
      (Effect.post
        (cmovR16M16Effect p (encodeCmovR16M16 cc dst am).length (dst.setWidth 5) am c)) := by
  unfold encodeCmovR16M16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := cmov_r16_m16_triple_of_bytes p cc (regLow dst) am hv hx hb c
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    rw [show (0x66 :: 0x0F :: cmovOpcode cc :: am.modrm (regLow dst) :: am.tail).length =
      4 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := cmov_r16_m16_rex_triple_of_bytes p cc _ hrex (regLow dst) am hv hx hb c
    rw [hr, gprNumber_reg] at this
    rw [show (0x66 :: am.rexByte false dst :: 0x0F :: cmovOpcode cc :: am.modrm (regLow dst) ::
      am.tail).length = 5 + am.tail.length by simp; omega]
    exact this

theorem cmov_r64_m64_seg_triple [Bindings] (p : BitVec 64) (cc : BitVec 4) (r : SegReg)
    (base : BitVec 64) (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s =>
        SegLoadPre p r base
          (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeCmovR64M64 cc dst am).length)) 8 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (r.prefixByte :: encodeCmovR64M64 cc dst am))
      (Effect.post
        (cmovR64M64SegEffect p (r.prefixByte :: encodeCmovR64M64 cc dst am).length base (dst.setWidth 5) am
          c)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := cmov_r64_m64_seg_triple_of_bytes p cc r base _ hrex (regLow dst) am hv hx hb c
  rw [hr, gprNumber_reg] at this
  unfold encodeCmovR64M64
  rw [show (r.prefixByte :: am.rexByte true dst :: 0x0F :: cmovOpcode cc :: am.modrm (regLow dst) ::
    am.tail).length = 5 + am.tail.length by simp; omega]
  exact this

theorem cmov_r32_m32_seg_triple [Bindings] (p : BitVec 64) (cc : BitVec 4) (r : SegReg)
    (base : BitVec 64) (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s =>
        SegLoadPre p r base
          (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeCmovR32M32 cc dst am).length)) 4 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (r.prefixByte :: encodeCmovR32M32 cc dst am))
      (Effect.post
        (cmovR32M32SegEffect p (r.prefixByte :: encodeCmovR32M32 cc dst am).length base (dst.setWidth 5) am
          c)) := by
  unfold encodeCmovR32M32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := cmov_r32_m32_seg_triple_of_bytes p cc r base (regLow dst) am hv hx hb c
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    rw [show (r.prefixByte :: 0x0F :: cmovOpcode cc :: am.modrm (regLow dst) :: am.tail).length =
      4 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := cmov_r32_m32_rex_seg_triple_of_bytes p cc r base _ hrex (regLow dst) am hv hx hb c
    rw [hr, gprNumber_reg] at this
    rw [show (r.prefixByte :: am.rexByte false dst :: 0x0F :: cmovOpcode cc ::
      am.modrm (regLow dst) :: am.tail).length = 5 + am.tail.length by simp; omega]
    exact this

theorem cmov_r16_m16_seg_triple [Bindings] (p : BitVec 64) (cc : BitVec 4) (r : SegReg)
    (base : BitVec 64) (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s =>
        SegLoadPre p r base
          (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeCmovR16M16 cc dst am).length)) 2 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (r.prefixByte :: encodeCmovR16M16 cc dst am))
      (Effect.post
        (cmovR16M16SegEffect p (r.prefixByte :: encodeCmovR16M16 cc dst am).length base (dst.setWidth 5) am
          c)) := by
  unfold encodeCmovR16M16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := cmov_r16_m16_seg_triple_of_bytes p cc r base (regLow dst) am hv hx hb c
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    rw [show (r.prefixByte :: 0x66 :: 0x0F :: cmovOpcode cc :: am.modrm (regLow dst) :: am.tail).length =
      5 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := cmov_r16_m16_rex_seg_triple_of_bytes p cc r base _ hrex (regLow dst) am hv hx hb c
    rw [hr, gprNumber_reg] at this
    rw [show (r.prefixByte :: 0x66 :: am.rexByte false dst :: 0x0F :: cmovOpcode cc ::
      am.modrm (regLow dst) :: am.tail).length = 6 + am.tail.length by simp; omega]
    exact this

theorem cmov_r64_m64_a32_triple [Bindings] (p : BitVec 64) (cc : BitVec 4) (dst : BitVec 4)
    (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s =>
        LoadPre p
          (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeCmovR64M64 cc dst am).length)) 8 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x67 :: encodeCmovR64M64 cc dst am))
      (Effect.post
        (cmovR64M64A32Effect p (0x67 :: encodeCmovR64M64 cc dst am).length (dst.setWidth 5) am c)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := cmov_r64_m64_a32_triple_of_bytes p cc _ hrex (regLow dst) am hv hx hb c
  rw [hr, gprNumber_reg] at this
  unfold encodeCmovR64M64
  rw [show (0x67 :: am.rexByte true dst :: 0x0F :: cmovOpcode cc :: am.modrm (regLow dst) ::
    am.tail).length = 5 + am.tail.length by simp; omega]
  exact this

theorem cmov_r32_m32_a32_triple [Bindings] (p : BitVec 64) (cc : BitVec 4) (dst : BitVec 4)
    (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s =>
        LoadPre p
          (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeCmovR32M32 cc dst am).length)) 4 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x67 :: encodeCmovR32M32 cc dst am))
      (Effect.post
        (cmovR32M32A32Effect p (0x67 :: encodeCmovR32M32 cc dst am).length (dst.setWidth 5) am c)) := by
  unfold encodeCmovR32M32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := cmov_r32_m32_a32_triple_of_bytes p cc (regLow dst) am hv hx hb c
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    rw [show (0x67 :: 0x0F :: cmovOpcode cc :: am.modrm (regLow dst) :: am.tail).length =
      4 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := cmov_r32_m32_rex_a32_triple_of_bytes p cc _ hrex (regLow dst) am hv hx hb c
    rw [hr, gprNumber_reg] at this
    rw [show (0x67 :: am.rexByte false dst :: 0x0F :: cmovOpcode cc ::
      am.modrm (regLow dst) :: am.tail).length = 5 + am.tail.length by simp; omega]
    exact this

theorem cmov_r16_m16_a32_triple [Bindings] (p : BitVec 64) (cc : BitVec 4) (dst : BitVec 4)
    (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s =>
        LoadPre p
          (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeCmovR16M16 cc dst am).length)) 2 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x67 :: encodeCmovR16M16 cc dst am))
      (Effect.post
        (cmovR16M16A32Effect p (0x67 :: encodeCmovR16M16 cc dst am).length (dst.setWidth 5) am c)) := by
  unfold encodeCmovR16M16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := cmov_r16_m16_a32_triple_of_bytes p cc (regLow dst) am hv hx hb c
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    rw [show (0x67 :: 0x66 :: 0x0F :: cmovOpcode cc :: am.modrm (regLow dst) :: am.tail).length =
      5 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := cmov_r16_m16_rex_a32_triple_of_bytes p cc _ hrex (regLow dst) am hv hx hb c
    rw [hr, gprNumber_reg] at this
    rw [show (0x67 :: 0x66 :: am.rexByte false dst :: 0x0F :: cmovOpcode cc ::
      am.modrm (regLow dst) :: am.tail).length = 6 + am.tail.length by simp; omega]
    exact this

attribute [x86_compose] cmovR64M64Effect cmovR32M32Effect cmovR16M16Effect cmovR64M64SegEffect cmovR32M32SegEffect cmovR16M16SegEffect cmovR64M64A32Effect cmovR32M32A32Effect cmovR16M16A32Effect

@[x86_local] theorem cmovR64M64Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} {c : Bool} :
    Effect.Local (cmovR64M64Effect p len dst am c) := by
  effect_local [cmovR64M64Effect]

@[x86_local] theorem cmovR64M64SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} {c : Bool} :
    Effect.Local (cmovR64M64SegEffect p len base dst am c) := by
  effect_local [cmovR64M64SegEffect]

@[x86_local] theorem cmovR64M64A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} {c : Bool} :
    Effect.Local (cmovR64M64A32Effect p len dst am c) := by
  effect_local [cmovR64M64A32Effect]

@[x86_local] theorem cmovR32M32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} {c : Bool} :
    Effect.Local (cmovR32M32Effect p len dst am c) := by
  effect_local [cmovR32M32Effect]

@[x86_local] theorem cmovR32M32SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} {c : Bool} :
    Effect.Local (cmovR32M32SegEffect p len base dst am c) := by
  effect_local [cmovR32M32SegEffect]

@[x86_local] theorem cmovR32M32A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} {c : Bool} :
    Effect.Local (cmovR32M32A32Effect p len dst am c) := by
  effect_local [cmovR32M32A32Effect]

@[x86_local] theorem cmovR16M16Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} {c : Bool} :
    Effect.Local (cmovR16M16Effect p len dst am c) := by
  effect_local [cmovR16M16Effect]

@[x86_local] theorem cmovR16M16SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} {c : Bool} :
    Effect.Local (cmovR16M16SegEffect p len base dst am c) := by
  effect_local [cmovR16M16SegEffect]

@[x86_local] theorem cmovR16M16A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} {c : Bool} :
    Effect.Local (cmovR16M16A32Effect p len dst am c) := by
  effect_local [cmovR16M16A32Effect]

end X86Proofs
