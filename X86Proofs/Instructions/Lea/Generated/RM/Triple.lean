import X86Proofs.Instructions.Lea.Generated.RM.Step
import X86Proofs.Instructions.Lea.Generated.RM.Encode
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def leaR32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    Effect :=
  let a := am.addr s (p + BitVec.ofNat 64 len)
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      (leaSpec 32 a).setWidth 64⟩] }

@[simp] theorem leaR32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (leaR32Effect p len dst am s).components = [.reg dst, .rip] := rfl

def leaR16Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    Effect :=
  let a := am.addr s (p + BitVec.ofNat 64 len)
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (leaSpec 16 a) ((Operand.reg dst : Operand 64).read s)⟩] }

@[simp] theorem leaR16Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (leaR16Effect p len dst am s).components = [.reg dst, .rip] := rfl

theorem lea_r32_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x8D :: am.modrm reg :: am.tail))
      (leaR32Effect p (2 + am.tail.length) (gprNumber 0 0 reg)
        am) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := lea_r32_m_step s h [] (by simp)
    (by simp) (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) reg am hv
    (by exact AddrContext.legacy _ am hx hb)
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep,
    ReadyToStep.afterStep_writeResult h _ _ (fun _ => leaSpec 32 (am.addrAt s (2 + am.tail.length))) _,
    ⟨afterStep_writeResult_rip h _ _ (fun _ => leaSpec 32 (am.addrAt s (2 + am.tail.length))) _, ?_,
      trivial,
      AgreesExcept.afterStep_writeResult s _ _ (fun _ => leaSpec 32 (am.addrAt s (2 + am.tail.length)))
        _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32]
  rfl

theorem lea_r32_triple_of_bytes [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (fun s => s.RIP = p) (codeRange p (0x8D :: am.modrm reg :: am.tail))
      (Effect.post (leaR32Effect p (2 + am.tail.length) (gprNumber 0 0 reg)
        am)) :=
  Triple.of_effect (fun s _ => Effect.avoids_of_components_reg_rip
    (leaR32Effect_components _ _ _ am s) _)
    (lea_r32_effect_step p reg am hv hx hb)

theorem lea_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0x8D :: am.modrm reg :: am.tail))
      (leaR32Effect p (3 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := lea_r32_m_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp) (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_rex _ _ hr]; exact AddrContext.rex _ _ am hx hb)
    hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep,
    ReadyToStep.afterStep_writeResult h _ _ (fun _ => leaSpec 32 (am.addrAt s (3 + am.tail.length))) _,
    ⟨afterStep_writeResult_rip h _ _ (fun _ => leaSpec 32 (am.addrAt s (3 + am.tail.length))) _, ?_,
      trivial,
      AgreesExcept.afterStep_writeResult s _ _ (fun _ => leaSpec 32 (am.addrAt s (3 + am.tail.length)))
        _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32]
  rfl

theorem lea_r32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: 0x8D :: am.modrm reg :: am.tail))
      (Effect.post (leaR32Effect p (3 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun s _ => Effect.avoids_of_components_reg_rip
    (leaR32Effect_components _ _ _ am s) _)
    (lea_r32_rex_effect_step p rex hrex reg am hv hx hb)

theorem lea_r16_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x66 :: 0x8D :: am.modrm reg :: am.tail))
      (leaR16Effect p (3 + am.tail.length) (gprNumber 0 0 reg)
        am) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := lea_r16_m_step s h [0x66] (by simpa using scanPrefix_66)
    (by simp) (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) reg am hv
    (by exact AddrContext.osz _ am hx hb)
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep,
    ReadyToStep.afterStep_writeResult h _ _ (fun _ => leaSpec 16 (am.addrAt s (3 + am.tail.length))) _,
    ⟨afterStep_writeResult_rip h _ _ (fun _ => leaSpec 16 (am.addrAt s (3 + am.tail.length))) _, ?_,
      trivial,
      AgreesExcept.afterStep_writeResult s _ _ (fun _ => leaSpec 16 (am.addrAt s (3 + am.tail.length)))
        _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch]
  rfl

theorem lea_r16_triple_of_bytes [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (fun s => s.RIP = p) (codeRange p (0x66 :: 0x8D :: am.modrm reg :: am.tail))
      (Effect.post (leaR16Effect p (3 + am.tail.length) (gprNumber 0 0 reg)
        am)) :=
  Triple.of_effect (fun s _ => Effect.avoids_of_components_reg_rip
    (leaR16Effect_components _ _ _ am s) _)
    (lea_r16_effect_step p reg am hv hx hb)

theorem lea_r16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x66 :: rex :: 0x8D :: am.modrm reg :: am.tail))
      (leaR16Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := lea_r16_m_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix])
    (by simp) (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_66_rex _ _ hr]; exact AddrContext.oszRex _ _ am hx hb)
    hcode.bytesAt hlow
  simp only [scanContext_66_rex _ _ hr] at hstep
  have hdst : gprNumber (oszRexContext s.DS rex.toBitVec).rex_r4
      (oszRexContext s.DS rex.toBitVec).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep,
    ReadyToStep.afterStep_writeResult h _ _ (fun _ => leaSpec 16 (am.addrAt s (4 + am.tail.length))) _,
    ⟨afterStep_writeResult_rip h _ _ (fun _ => leaSpec 16 (am.addrAt s (4 + am.tail.length))) _, ?_,
      trivial,
      AgreesExcept.afterStep_writeResult s _ _ (fun _ => leaSpec 16 (am.addrAt s (4 + am.tail.length)))
        _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch]
  rfl

theorem lea_r16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => s.RIP = p) (codeRange p (0x66 :: rex :: 0x8D :: am.modrm reg :: am.tail))
      (Effect.post (leaR16Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun s _ => Effect.avoids_of_components_reg_rip
    (leaR16Effect_components _ _ _ am s) _)
    (lea_r16_rex_effect_step p rex hrex reg am hv hx hb)

theorem lea_r32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeLeaR32M dst am))
      (Effect.post (leaR32Effect p (encodeLeaR32M dst am).length (dst.setWidth 5) am)) := by
  unfold encodeLeaR32M
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := lea_r32_triple_of_bytes p (regLow dst) am hv hx hb
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 = 2 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := lea_r32_rex_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]

theorem lea_r16_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeLeaR16M dst am))
      (Effect.post (leaR16Effect p (encodeLeaR16M dst am).length (dst.setWidth 5) am)) := by
  unfold encodeLeaR16M
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := lea_r16_triple_of_bytes p (regLow dst) am hv hx hb
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := lea_r16_rex_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

attribute [x86_compose] leaR32Effect leaR16Effect

@[x86_local] theorem leaR32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (leaR32Effect p len dst am) := by
  effect_local [leaR32Effect, leaSpec]

@[x86_local] theorem leaR16Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (leaR16Effect p len dst am) := by
  effect_local [leaR16Effect, leaSpec]

def leaR64A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    Effect :=
  let a := am.addr32 s (p + BitVec.ofNat 64 len)
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      a⟩] }

@[simp] theorem leaR64A32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (leaR64A32Effect p len dst am s).components = [.reg dst, .rip] := rfl

def leaR32A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    Effect :=
  let a := am.addr32 s (p + BitVec.ofNat 64 len)
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      (leaSpec 32 a).setWidth 64⟩] }

@[simp] theorem leaR32A32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (leaR32A32Effect p len dst am s).components = [.reg dst, .rip] := rfl

def leaR16A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    Effect :=
  let a := am.addr32 s (p + BitVec.ofNat 64 len)
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (leaSpec 16 a) ((Operand.reg dst : Operand 64).read s)⟩] }

@[simp] theorem leaR16A32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (leaR16A32Effect p len dst am s).components = [.reg dst, .rip] := rfl

theorem lea_r64_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x67 :: rex :: 0x8D :: am.modrm reg :: am.tail))
      (leaR64A32Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := lea_r64_m_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix))
    (by simp) (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withAsz)
    hcode.bytesAt hlow
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (rexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (rexContext s.DS rex.toBitVec)).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep,
    ReadyToStep.afterStep_writeResult h _ _ (fun _ => am.addrAt32 s (4 + am.tail.length)) _,
    ⟨afterStep_writeResult_rip h _ _ (fun _ => am.addrAt32 s (4 + am.tail.length)) _, ?_,
      trivial,
      AgreesExcept.afterStep_writeResult s _ _ (fun _ => am.addrAt32 s (4 + am.tail.length))
        _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self]
  rfl

theorem lea_r64_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => s.RIP = p) (codeRange p (0x67 :: rex :: 0x8D :: am.modrm reg :: am.tail))
      (Effect.post (leaR64A32Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun s _ => Effect.avoids_of_components_reg_rip
    (leaR64A32Effect_components _ _ _ am s) _)
    (lea_r64_a32_effect_step p rex hrex reg am hv hx hb)

theorem lea_r32_a32_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x67 :: 0x8D :: am.modrm reg :: am.tail))
      (leaR32A32Effect p (3 + am.tail.length) (gprNumber 0 0 reg)
        am) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := lea_r32_m_a32_step s h [0x67] (scanPrefix_asz_cons (by simp))
    (by simp) (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withAsz)
    hcode.bytesAt hlow
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r4
      (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep,
    ReadyToStep.afterStep_writeResult h _ _ (fun _ => leaSpec 32 (am.addrAt32 s (3 + am.tail.length))) _,
    ⟨afterStep_writeResult_rip h _ _ (fun _ => leaSpec 32 (am.addrAt32 s (3 + am.tail.length))) _, ?_,
      trivial,
      AgreesExcept.afterStep_writeResult s _ _ (fun _ => leaSpec 32 (am.addrAt32 s (3 + am.tail.length)))
        _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32]
  rfl

theorem lea_r32_a32_triple_of_bytes [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (fun s => s.RIP = p) (codeRange p (0x67 :: 0x8D :: am.modrm reg :: am.tail))
      (Effect.post (leaR32A32Effect p (3 + am.tail.length) (gprNumber 0 0 reg)
        am)) :=
  Triple.of_effect (fun s _ => Effect.avoids_of_components_reg_rip
    (leaR32A32Effect_components _ _ _ am s) _)
    (lea_r32_a32_effect_step p reg am hv hx hb)

theorem lea_r32_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x67 :: rex :: 0x8D :: am.modrm reg :: am.tail))
      (leaR32A32Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := lea_r32_m_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix))
    (by simp) (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withAsz)
    hcode.bytesAt hlow
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (rexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (rexContext s.DS rex.toBitVec)).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep,
    ReadyToStep.afterStep_writeResult h _ _ (fun _ => leaSpec 32 (am.addrAt32 s (4 + am.tail.length))) _,
    ⟨afterStep_writeResult_rip h _ _ (fun _ => leaSpec 32 (am.addrAt32 s (4 + am.tail.length))) _, ?_,
      trivial,
      AgreesExcept.afterStep_writeResult s _ _ (fun _ => leaSpec 32 (am.addrAt32 s (4 + am.tail.length)))
        _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32]
  rfl

theorem lea_r32_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => s.RIP = p) (codeRange p (0x67 :: rex :: 0x8D :: am.modrm reg :: am.tail))
      (Effect.post (leaR32A32Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun s _ => Effect.avoids_of_components_reg_rip
    (leaR32A32Effect_components _ _ _ am s) _)
    (lea_r32_rex_a32_effect_step p rex hrex reg am hv hx hb)

theorem lea_r16_a32_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x67 :: 0x66 :: 0x8D :: am.modrm reg :: am.tail))
      (leaR16A32Effect p (4 + am.tail.length) (gprNumber 0 0 reg)
        am) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66]) := by
    rw [scanContext_asz_cons]
  have hstep := lea_r16_m_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66))
    (by simp) (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).withAsz)
    hcode.bytesAt hlow
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66])).rex_r4
      (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66])).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep,
    ReadyToStep.afterStep_writeResult h _ _ (fun _ => leaSpec 16 (am.addrAt32 s (4 + am.tail.length))) _,
    ⟨afterStep_writeResult_rip h _ _ (fun _ => leaSpec 16 (am.addrAt32 s (4 + am.tail.length))) _, ?_,
      trivial,
      AgreesExcept.afterStep_writeResult s _ _ (fun _ => leaSpec 16 (am.addrAt32 s (4 + am.tail.length)))
        _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch]
  rfl

theorem lea_r16_a32_triple_of_bytes [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (fun s => s.RIP = p) (codeRange p (0x67 :: 0x66 :: 0x8D :: am.modrm reg :: am.tail))
      (Effect.post (leaR16A32Effect p (4 + am.tail.length) (gprNumber 0 0 reg)
        am)) :=
  Triple.of_effect (fun s _ => Effect.avoids_of_components_reg_rip
    (leaR16A32Effect_components _ _ _ am s) _)
    (lea_r16_a32_effect_step p reg am hv hx hb)

theorem lea_r16_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x67 :: 0x66 :: rex :: 0x8D :: am.modrm reg :: am.tail))
      (leaR16A32Effect p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66, rex] =
      withAsz (oszRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_66_rex _ _ hr]
  have hstep := lea_r16_m_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix]))
    (by simp) (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).withAsz)
    hcode.bytesAt hlow
  simp only [hsc] at hstep
  have hdst : gprNumber (withAsz (oszRexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (oszRexContext s.DS rex.toBitVec)).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep,
    ReadyToStep.afterStep_writeResult h _ _ (fun _ => leaSpec 16 (am.addrAt32 s (5 + am.tail.length))) _,
    ⟨afterStep_writeResult_rip h _ _ (fun _ => leaSpec 16 (am.addrAt32 s (5 + am.tail.length))) _, ?_,
      trivial,
      AgreesExcept.afterStep_writeResult s _ _ (fun _ => leaSpec 16 (am.addrAt32 s (5 + am.tail.length)))
        _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch]
  rfl

theorem lea_r16_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => s.RIP = p) (codeRange p (0x67 :: 0x66 :: rex :: 0x8D :: am.modrm reg :: am.tail))
      (Effect.post (leaR16A32Effect p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun s _ => Effect.avoids_of_components_reg_rip
    (leaR16A32Effect_components _ _ _ am s) _)
    (lea_r16_rex_a32_effect_step p rex hrex reg am hv hx hb)

theorem lea_r64_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (fun s => s.RIP = p) (codeRange p (0x67 :: encodeLeaR64M dst am))
      (Effect.post (leaR64A32Effect p (0x67 :: encodeLeaR64M dst am).length (dst.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := lea_r64_a32_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
  rw [hr, gprNumber_reg] at this
  unfold encodeLeaR64M
  simp only [List.length_cons]
  rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem lea_r32_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (fun s => s.RIP = p) (codeRange p (0x67 :: encodeLeaR32M dst am))
      (Effect.post (leaR32A32Effect p (0x67 :: encodeLeaR32M dst am).length (dst.setWidth 5) am)) := by
  unfold encodeLeaR32M
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := lea_r32_a32_triple_of_bytes p (regLow dst) am hv hx hb
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := lea_r32_rex_a32_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem lea_r16_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (fun s => s.RIP = p) (codeRange p (0x67 :: encodeLeaR16M dst am))
      (Effect.post (leaR16A32Effect p (0x67 :: encodeLeaR16M dst am).length (dst.setWidth 5) am)) := by
  unfold encodeLeaR16M
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := lea_r16_a32_triple_of_bytes p (regLow dst) am hv hx hb
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := lea_r16_rex_a32_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

attribute [x86_compose] leaR64A32Effect leaR32A32Effect leaR16A32Effect

@[x86_local] theorem leaR64A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (leaR64A32Effect p len dst am) := by
  effect_local [leaR64A32Effect]

@[x86_local] theorem leaR32A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (leaR32A32Effect p len dst am) := by
  effect_local [leaR32A32Effect, leaSpec]

@[x86_local] theorem leaR16A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (leaR16A32Effect p len dst am) := by
  effect_local [leaR16A32Effect, leaSpec]

end X86Proofs
