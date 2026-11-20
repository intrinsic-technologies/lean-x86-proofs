import X86Proofs.Instructions.Bt.Generated.MImm8.Step
import X86Proofs.Instructions.Bt.Generated.MImm8.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def btM64Imm8Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8)
    (s : RamState) : Effect :=
  let addr := am.addr s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand 64).read s
  let b := imm.signExtend 64
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (btFlags (StatusFlags.ofRFLAGS s.RFLAGS) a b) }

@[simp] theorem btM64Imm8Effect_components (p : BitVec 64) (len : Nat)
    (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    (btM64Imm8Effect p len am imm s).components =
      [.flags, .rip] := rfl

def btM64Imm8SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode) (imm : BitVec 8)
    (s : RamState) : Effect :=
  let addr := base + am.addr s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand 64).read s
  let b := imm.signExtend 64
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (btFlags (StatusFlags.ofRFLAGS s.RFLAGS) a b) }

@[simp] theorem btM64Imm8SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    (btM64Imm8SegEffect p len base am imm s).components =
      [.flags, .rip] := rfl

def btM64Imm8A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    Effect :=
  let addr := am.addr32 s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand 64).read s
  let b := imm.signExtend 64
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (btFlags (StatusFlags.ofRFLAGS s.RFLAGS) a b) }

@[simp] theorem btM64Imm8A32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (imm : BitVec 8) (s : RamState) :
    (btM64Imm8A32Effect p len am imm s).components =
      [.flags, .rip] := rfl

def btM32Imm8Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8)
    (s : RamState) : Effect :=
  let addr := am.addr s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand 32).read s
  let b := imm.signExtend 32
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (btFlags (StatusFlags.ofRFLAGS s.RFLAGS) a b) }

@[simp] theorem btM32Imm8Effect_components (p : BitVec 64) (len : Nat)
    (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    (btM32Imm8Effect p len am imm s).components =
      [.flags, .rip] := rfl

def btM32Imm8SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode) (imm : BitVec 8)
    (s : RamState) : Effect :=
  let addr := base + am.addr s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand 32).read s
  let b := imm.signExtend 32
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (btFlags (StatusFlags.ofRFLAGS s.RFLAGS) a b) }

@[simp] theorem btM32Imm8SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    (btM32Imm8SegEffect p len base am imm s).components =
      [.flags, .rip] := rfl

def btM32Imm8A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    Effect :=
  let addr := am.addr32 s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand 32).read s
  let b := imm.signExtend 32
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (btFlags (StatusFlags.ofRFLAGS s.RFLAGS) a b) }

@[simp] theorem btM32Imm8A32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (imm : BitVec 8) (s : RamState) :
    (btM32Imm8A32Effect p len am imm s).components =
      [.flags, .rip] := rfl

def btM16Imm8Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8)
    (s : RamState) : Effect :=
  let addr := am.addr s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand 16).read s
  let b := imm.signExtend 16
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (btFlags (StatusFlags.ofRFLAGS s.RFLAGS) a b) }

@[simp] theorem btM16Imm8Effect_components (p : BitVec 64) (len : Nat)
    (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    (btM16Imm8Effect p len am imm s).components =
      [.flags, .rip] := rfl

def btM16Imm8SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode) (imm : BitVec 8)
    (s : RamState) : Effect :=
  let addr := base + am.addr s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand 16).read s
  let b := imm.signExtend 16
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (btFlags (StatusFlags.ofRFLAGS s.RFLAGS) a b) }

@[simp] theorem btM16Imm8SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    (btM16Imm8SegEffect p len base am imm s).components =
      [.flags, .rip] := rfl

def btM16Imm8A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (s : RamState) :
    Effect :=
  let addr := am.addr32 s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand 16).read s
  let b := imm.signExtend 16
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (btFlags (StatusFlags.ofRFLAGS s.RFLAGS) a b) }

@[simp] theorem btM16Imm8A32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (imm : BitVec 8) (s : RamState) :
    (btM16Imm8A32Effect p len am imm s).components =
      [.flags, .rip] := rfl

theorem bt_m64_imm8_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
      (codeRange p (rex :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (btM64Imm8Effect p (5 + am.tail.length) am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := bt_m_imm8_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  exact btFlags_allows _ _ _ _

theorem bt_m64_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
      (codeRange p (rex :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (btM64Imm8Effect p (5 + am.tail.length) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btM64Imm8Effect_components]; simp [Component.Covers]) _)
    (bt_m64_imm8_effect_step p rex hrex am hv hx hb imm)

theorem bt_m32_imm8_effect_step [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (btM32Imm8Effect p (4 + am.tail.length) am imm) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := bt_m_imm8_step s h [] (by simp) (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  exact btFlags_allows _ _ _ _

theorem bt_m32_imm8_triple_of_bytes [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (btM32Imm8Effect p (4 + am.tail.length) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btM32Imm8Effect_components]; simp [Component.Covers]) _)
    (bt_m32_imm8_effect_step p am hv hx hb imm)

theorem bt_m32_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4)
      (codeRange p (rex :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (btM32Imm8Effect p (5 + am.tail.length) am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := bt_m_imm8_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  exact btFlags_allows _ _ _ _

theorem bt_m32_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4)
      (codeRange p (rex :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (btM32Imm8Effect p (5 + am.tail.length) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btM32Imm8Effect_components]; simp [Component.Covers]) _)
    (bt_m32_imm8_rex_effect_step p rex hrex am hv hx hb imm)

theorem bt_m16_imm8_effect_step [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (0x66 :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (btM16Imm8Effect p (5 + am.tail.length) am imm) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := bt_m16_imm8_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) am hv
    (by exact (AddrContext.osz _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  exact btFlags_allows _ _ _ _

theorem bt_m16_imm8_triple_of_bytes [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (0x66 :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (btM16Imm8Effect p (5 + am.tail.length) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btM16Imm8Effect_components]; simp [Component.Covers]) _)
    (bt_m16_imm8_effect_step p am hv hx hb imm)

theorem bt_m16_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2)
      (codeRange p (0x66 :: rex :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (btM16Imm8Effect p (6 + am.tail.length) am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := bt_m16_imm8_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_66_rex _ _ hr]; exact (AddrContext.oszRex _ _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_66_rex _ _ hr]; exact hread)
  simp only [scanContext_66_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  exact btFlags_allows _ _ _ _

theorem bt_m16_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2)
      (codeRange p (0x66 :: rex :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (btM16Imm8Effect p (6 + am.tail.length) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btM16Imm8Effect_components]; simp [Component.Covers]) _)
    (bt_m16_imm8_rex_effect_step p rex hrex am hv hx hb imm)

theorem bt_m64_imm8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 8)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (btM64Imm8SegEffect p (6 + am.tail.length) base am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := bt_m_imm8_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  exact btFlags_allows _ _ _ _

theorem bt_m64_imm8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 8)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (btM64Imm8SegEffect p (6 + am.tail.length) base am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btM64Imm8SegEffect_components]; simp [Component.Covers]) _)
    (bt_m64_imm8_seg_effect_step p r base rex hrex am hv hx hb imm)

theorem bt_m32_imm8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (btM32Imm8SegEffect p (5 + am.tail.length) base am imm) := by
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := bt_m_imm8_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  exact btFlags_allows _ _ _ _

theorem bt_m32_imm8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (btM32Imm8SegEffect p (5 + am.tail.length) base am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btM32Imm8SegEffect_components]; simp [Component.Covers]) _)
    (bt_m32_imm8_seg_effect_step p r base am hv hx hb imm)

theorem bt_m32_imm8_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (btM32Imm8SegEffect p (6 + am.tail.length) base am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := bt_m_imm8_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  exact btFlags_allows _ _ _ _

theorem bt_m32_imm8_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (btM32Imm8SegEffect p (6 + am.tail.length) base am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btM32Imm8SegEffect_components]; simp [Component.Covers]) _)
    (bt_m32_imm8_rex_seg_effect_step p r base rex hrex am hv hx hb imm)

theorem bt_m16_imm8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (btM16Imm8SegEffect p (6 + am.tail.length) base am imm) := by
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66]
      (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil)]
  have hstep := bt_m16_imm8_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  exact btFlags_allows _ _ _ _

theorem bt_m16_imm8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (btM16Imm8SegEffect p (6 + am.tail.length) base am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btM16Imm8SegEffect_components]; simp [Component.Covers]) _)
    (bt_m16_imm8_seg_effect_step p r base am hv hx hb imm)

theorem bt_m16_imm8_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (7 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (btM16Imm8SegEffect p (7 + am.tail.length) base am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66, rex] =
      withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66, rex]
      (noSegPrefix_cons noSegPrefix_66 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_66_rex _ _ hr]
  have hstep := bt_m16_imm8_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  exact btFlags_allows _ _ _ _

theorem bt_m16_imm8_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (7 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (btM16Imm8SegEffect p (7 + am.tail.length) base am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btM16Imm8SegEffect_components]; simp [Component.Covers]) _)
    (bt_m16_imm8_rex_seg_effect_step p r base rex hrex am hv hx hb imm)

theorem bt_m64_imm8_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 8)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (btM64Imm8A32Effect p (6 + am.tail.length) am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := bt_m_imm8_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  exact btFlags_allows _ _ _ _

theorem bt_m64_imm8_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 8)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (btM64Imm8A32Effect p (6 + am.tail.length) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btM64Imm8A32Effect_components]; simp [Component.Covers]) _)
    (bt_m64_imm8_a32_effect_step p rex hrex am hv hx hb imm)

theorem bt_m32_imm8_a32_effect_step [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4)
      (codeRange p (0x67 :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (btM32Imm8A32Effect p (5 + am.tail.length) am imm) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := bt_m_imm8_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  exact btFlags_allows _ _ _ _

theorem bt_m32_imm8_a32_triple_of_bytes [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4)
      (codeRange p (0x67 :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (btM32Imm8A32Effect p (5 + am.tail.length) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btM32Imm8A32Effect_components]; simp [Component.Covers]) _)
    (bt_m32_imm8_a32_effect_step p am hv hx hb imm)

theorem bt_m32_imm8_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 4)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (btM32Imm8A32Effect p (6 + am.tail.length) am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := bt_m_imm8_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  exact btFlags_allows _ _ _ _

theorem bt_m32_imm8_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 4)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (btM32Imm8A32Effect p (6 + am.tail.length) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btM32Imm8A32Effect_components]; simp [Component.Covers]) _)
    (bt_m32_imm8_rex_a32_effect_step p rex hrex am hv hx hb imm)

theorem bt_m16_imm8_a32_effect_step [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (btM16Imm8A32Effect p (6 + am.tail.length) am imm) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66]) := by
    rw [scanContext_asz_cons]
  have hstep := bt_m16_imm8_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  exact btFlags_allows _ _ _ _

theorem bt_m16_imm8_a32_triple_of_bytes [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (btM16Imm8A32Effect p (6 + am.tail.length) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btM16Imm8A32Effect_components]; simp [Component.Covers]) _)
    (bt_m16_imm8_a32_effect_step p am hv hx hb imm)

theorem bt_m16_imm8_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (7 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (btM16Imm8A32Effect p (7 + am.tail.length) am imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66, rex] =
      withAsz (oszRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_66_rex _ _ hr]
  have hstep := bt_m16_imm8_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  exact btFlags_allows _ _ _ _

theorem bt_m16_imm8_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (7 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (btM16Imm8A32Effect p (7 + am.tail.length) am imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btM16Imm8A32Effect_components]; simp [Component.Covers]) _)
    (bt_m16_imm8_rex_a32_effect_step p rex hrex am hv hx hb imm)

theorem bt_m64_imm8_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 8)
      (codeRange p (encodeBtM64Imm8 am imm))
      (Effect.post (btM64Imm8Effect p (5 + am.tail.length) am imm)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact bt_m64_imm8_triple_of_bytes p _ hrex am hv hx hb imm

theorem bt_m32_imm8_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (encodeBtM32Imm8 am imm).length)) 4)
      (codeRange p (encodeBtM32Imm8 am imm))
      (Effect.post (btM32Imm8Effect p (encodeBtM32Imm8 am imm).length am imm)) := by
  unfold encodeBtM32Imm8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := bt_m32_imm8_triple_of_bytes p am hv hx hb imm
    rwa [show (0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)).length =
      4 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := bt_m32_imm8_rex_triple_of_bytes p _ hrex am hv hx hb imm
    rwa [show (am.rexByte false 0 :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)).length =
      5 + am.tail.length by simp; omega]

theorem bt_m16_imm8_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (encodeBtM16Imm8 am imm).length)) 2)
      (codeRange p (encodeBtM16Imm8 am imm))
      (Effect.post (btM16Imm8Effect p (encodeBtM16Imm8 am imm).length am imm)) := by
  unfold encodeBtM16Imm8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := bt_m16_imm8_triple_of_bytes p am hv hx hb imm
    rwa [show (0x66 :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)).length =
      5 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := bt_m16_imm8_rex_triple_of_bytes p _ hrex am hv hx hb imm
    rwa [show (0x66 :: am.rexByte false 0 :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)).length =
      6 + am.tail.length by simp; omega]

theorem bt_m64_imm8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (imm : BitVec 8) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 8)
      (codeRange p (r.prefixByte :: encodeBtM64Imm8 am imm))
      (Effect.post (btM64Imm8SegEffect p (6 + am.tail.length) base am imm)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact bt_m64_imm8_seg_triple_of_bytes p r base _ hrex am hv hx hb imm

theorem bt_m32_imm8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (imm : BitVec 8) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeBtM32Imm8 am imm).length)) 4)
      (codeRange p (r.prefixByte :: encodeBtM32Imm8 am imm))
      (Effect.post (btM32Imm8SegEffect p (r.prefixByte :: encodeBtM32Imm8 am imm).length base am imm)) := by
  unfold encodeBtM32Imm8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := bt_m32_imm8_seg_triple_of_bytes p r base am hv hx hb imm
    rwa [show (r.prefixByte :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)).length =
      5 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := bt_m32_imm8_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb imm
    rwa [show (r.prefixByte :: am.rexByte false 0 :: 0x0F :: 0xBA :: am.modrm 4 ::
      (am.tail ++ immBytes 8 imm)).length = 6 + am.tail.length by simp; omega]

theorem bt_m16_imm8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (imm : BitVec 8) :
    Triple (SegLoadPre p r base (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeBtM16Imm8 am imm).length)) 2)
      (codeRange p (r.prefixByte :: encodeBtM16Imm8 am imm))
      (Effect.post (btM16Imm8SegEffect p (r.prefixByte :: encodeBtM16Imm8 am imm).length base am imm)) := by
  unfold encodeBtM16Imm8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := bt_m16_imm8_seg_triple_of_bytes p r base am hv hx hb imm
    rwa [show (r.prefixByte :: 0x66 :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)).length =
      6 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := bt_m16_imm8_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb imm
    rwa [show (r.prefixByte :: 0x66 :: am.rexByte false 0 :: 0x0F :: 0xBA :: am.modrm 4 ::
      (am.tail ++ immBytes 8 imm)).length = 7 + am.tail.length by simp; omega]

theorem bt_m64_imm8_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (6 + am.tail.length))) 8)
      (codeRange p (0x67 :: encodeBtM64Imm8 am imm))
      (Effect.post (btM64Imm8A32Effect p (6 + am.tail.length) am imm)) := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact bt_m64_imm8_a32_triple_of_bytes p _ hrex am hv hx hb imm

theorem bt_m32_imm8_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeBtM32Imm8 am imm).length)) 4)
      (codeRange p (0x67 :: encodeBtM32Imm8 am imm))
      (Effect.post (btM32Imm8A32Effect p (0x67 :: encodeBtM32Imm8 am imm).length am imm)) := by
  unfold encodeBtM32Imm8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := bt_m32_imm8_a32_triple_of_bytes p am hv hx hb imm
    rwa [show (0x67 :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)).length =
      5 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := bt_m32_imm8_rex_a32_triple_of_bytes p _ hrex am hv hx hb imm
    rwa [show (0x67 :: am.rexByte false 0 :: 0x0F :: 0xBA :: am.modrm 4 ::
      (am.tail ++ immBytes 8 imm)).length = 6 + am.tail.length by simp; omega]

theorem bt_m16_imm8_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 8) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeBtM16Imm8 am imm).length)) 2)
      (codeRange p (0x67 :: encodeBtM16Imm8 am imm))
      (Effect.post (btM16Imm8A32Effect p (0x67 :: encodeBtM16Imm8 am imm).length am imm)) := by
  unfold encodeBtM16Imm8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := bt_m16_imm8_a32_triple_of_bytes p am hv hx hb imm
    rwa [show (0x67 :: 0x66 :: 0x0F :: 0xBA :: am.modrm 4 :: (am.tail ++ immBytes 8 imm)).length =
      6 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := bt_m16_imm8_rex_a32_triple_of_bytes p _ hrex am hv hx hb imm
    rwa [show (0x67 :: 0x66 :: am.rexByte false 0 :: 0x0F :: 0xBA :: am.modrm 4 ::
      (am.tail ++ immBytes 8 imm)).length = 7 + am.tail.length by simp; omega]

attribute [x86_compose] btM64Imm8Effect btM32Imm8Effect btM16Imm8Effect btM64Imm8SegEffect btM32Imm8SegEffect btM16Imm8SegEffect btM64Imm8A32Effect btM32Imm8A32Effect btM16Imm8A32Effect

@[x86_local] theorem btM64Imm8Effect_local {p : BitVec 64} {len : Nat}
    {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (btM64Imm8Effect p len am imm) := by
  effect_local [btM64Imm8Effect, btFlags]

@[x86_local] theorem btM64Imm8SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (btM64Imm8SegEffect p len base am imm) := by
  effect_local [btM64Imm8SegEffect, btFlags]

@[x86_local] theorem btM64Imm8A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode}
    {imm : BitVec 8} :
    Effect.Local (btM64Imm8A32Effect p len am imm) := by
  effect_local [btM64Imm8A32Effect, btFlags]

@[x86_local] theorem btM32Imm8Effect_local {p : BitVec 64} {len : Nat}
    {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (btM32Imm8Effect p len am imm) := by
  effect_local [btM32Imm8Effect, btFlags]

@[x86_local] theorem btM32Imm8SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (btM32Imm8SegEffect p len base am imm) := by
  effect_local [btM32Imm8SegEffect, btFlags]

@[x86_local] theorem btM32Imm8A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode}
    {imm : BitVec 8} :
    Effect.Local (btM32Imm8A32Effect p len am imm) := by
  effect_local [btM32Imm8A32Effect, btFlags]

@[x86_local] theorem btM16Imm8Effect_local {p : BitVec 64} {len : Nat}
    {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (btM16Imm8Effect p len am imm) := by
  effect_local [btM16Imm8Effect, btFlags]

@[x86_local] theorem btM16Imm8SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {imm : BitVec 8} :
    Effect.Local (btM16Imm8SegEffect p len base am imm) := by
  effect_local [btM16Imm8SegEffect, btFlags]

@[x86_local] theorem btM16Imm8A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode}
    {imm : BitVec 8} :
    Effect.Local (btM16Imm8A32Effect p len am imm) := by
  effect_local [btM16Imm8A32Effect, btFlags]

end X86Proofs
