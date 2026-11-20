import X86Proofs.Instructions.Cmp.Generated.RM.Step
import X86Proofs.Instructions.Cmp.Generated.RM.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cmpR64M64Effect (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 (movLoadLen am)
    writes := []
    flags := some (.ofStatusFlags (cmpSpec a b)) }

@[simp] theorem cmpR64M64Effect_components (p : BitVec 64) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) : (cmpR64M64Effect p dst am s).components = [.flags, .rip] := rfl

def cmpR32M32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (.ofStatusFlags (cmpSpec a b)) }

@[simp] theorem cmpR32M32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) : (cmpR32M32Effect p len dst am s).components = [.flags, .rip] := rfl

def cmpR16M16Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  let b := (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (.ofStatusFlags (cmpSpec a b)) }

@[simp] theorem cmpR16M16Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) : (cmpR16M16Effect p len dst am s).components = [.flags, .rip] := rfl

theorem cmp_r64_m64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) 8)
      (codeRange p (rex :: 0x3B :: am.modrm reg :: am.tail))
      (cmpR64M64Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := cmp_r_m_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_r64_m64_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) 8)
      (codeRange p (rex :: 0x3B :: am.modrm reg :: am.tail))
      (Effect.post (cmpR64M64Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpR64M64Effect_components]; simp [Component.Covers]) _)
    (cmp_r64_m64_effect_step p rex hrex reg am hv hx hb)

theorem cmp_r32_m32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 4)
      (codeRange p (0x3B :: am.modrm reg :: am.tail))
      (cmpR32M32Effect p (2 + am.tail.length) (gprNumber 0 0 reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := cmp_r_m_step s h [] (by simp) (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) reg am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_r32_m32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 4)
      (codeRange p (0x3B :: am.modrm reg :: am.tail))
      (Effect.post (cmpR32M32Effect p (2 + am.tail.length) (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpR32M32Effect_components]; simp [Component.Covers]) _)
    (cmp_r32_m32_effect_step p reg am hv hx hb)

theorem cmp_r32_m32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (rex :: 0x3B :: am.modrm reg :: am.tail))
      (cmpR32M32Effect p (3 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := cmp_r_m_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_r32_m32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (rex :: 0x3B :: am.modrm reg :: am.tail))
      (Effect.post (cmpR32M32Effect p (3 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpR32M32Effect_components]; simp [Component.Covers]) _)
    (cmp_r32_m32_rex_effect_step p rex hrex reg am hv hx hb)

theorem cmp_r16_m16_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 2)
      (codeRange p (0x66 :: 0x3B :: am.modrm reg :: am.tail))
      (cmpR16M16Effect p (3 + am.tail.length) (gprNumber 0 0 reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := cmp_r16_m16_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) reg am hv
    (by exact (AddrContext.osz _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_r16_m16_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 2)
      (codeRange p (0x66 :: 0x3B :: am.modrm reg :: am.tail))
      (Effect.post (cmpR16M16Effect p (3 + am.tail.length) (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpR16M16Effect_components]; simp [Component.Covers]) _)
    (cmp_r16_m16_effect_step p reg am hv hx hb)

theorem cmp_r16_m16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (0x66 :: rex :: 0x3B :: am.modrm reg :: am.tail))
      (cmpR16M16Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := cmp_r16_m16_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_66_rex _ _ hr]; exact (AddrContext.oszRex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_66_rex _ _ hr]; exact hread)
  simp only [scanContext_66_rex _ _ hr] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_r16_m16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (0x66 :: rex :: 0x3B :: am.modrm reg :: am.tail))
      (Effect.post (cmpR16M16Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpR16M16Effect_components]; simp [Component.Covers]) _)
    (cmp_r16_m16_rex_effect_step p rex hrex reg am hv hx hb)

theorem cmp_r64_m64_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) 8)
      (codeRange p (encodeCmpR64M64 dst am))
      (Effect.post (cmpR64M64Effect p (dst.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := cmp_r64_m64_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
  rwa [hr, gprNumber_reg] at this

theorem cmp_r32_m32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (encodeCmpR32M32 dst am).length)) 4)
      (codeRange p (encodeCmpR32M32 dst am))
      (Effect.post (cmpR32M32Effect p (encodeCmpR32M32 dst am).length (dst.setWidth 5) am)) := by
  unfold encodeCmpR32M32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := cmp_r32_m32_triple_of_bytes p (regLow dst) am hv hx hb
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 = 2 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := cmp_r32_m32_rex_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]

theorem cmp_r16_m16_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (encodeCmpR16M16 dst am).length)) 2)
      (codeRange p (encodeCmpR16M16 dst am))
      (Effect.post (cmpR16M16Effect p (encodeCmpR16M16 dst am).length (dst.setWidth 5) am)) := by
  unfold encodeCmpR16M16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := cmp_r16_m16_triple_of_bytes p (regLow dst) am hv hx hb
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := cmp_r16_m16_rex_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

attribute [x86_compose] cmpR64M64Effect cmpR32M32Effect cmpR16M16Effect

@[x86_local] theorem cmpR64M64Effect_local {p : BitVec 64} {dst : BitVec 5} {am : AddrMode} :
    Effect.Local (cmpR64M64Effect p dst am) := by
  effect_local [cmpR64M64Effect]

@[x86_local] theorem cmpR32M32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {am : AddrMode} :
    Effect.Local (cmpR32M32Effect p len dst am) := by
  effect_local [cmpR32M32Effect]

@[x86_local] theorem cmpR16M16Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} {am : AddrMode} :
    Effect.Local (cmpR16M16Effect p len dst am) := by
  effect_local [cmpR16M16Effect]

def cmpR64M64SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (.ofStatusFlags (cmpSpec a b)) }

@[simp] theorem cmpR64M64SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (cmpR64M64SegEffect p len base dst am s).components =
      [.flags, .rip] := rfl

theorem cmp_r64_m64_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegLoadPre p r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (r.prefixByte :: rex :: 0x3B :: am.modrm reg :: am.tail))
      (cmpR64M64SegEffect p (4 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg)
        am) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := cmp_r_m_step s h [r.prefixByte, rex] (by simp [r.scanPrefix, hr.scanPrefix])
    (by simp) 64 (.inl rfl)
    (by rw [scanContext_seg_rex _ _ r hr]; exact hrex.operand_size_seg _ _)
    (by rw [scanContext_seg_rex _ _ r hr]; rfl) (by rw [scanContext_seg_rex _ _ r hr]; rfl)
    (by rw [scanContext_seg_rex _ _ r hr]; rfl) reg am hv
    (by rw [scanContext_seg_rex _ _ r hr]; exact SegAddrContext.seg_rex _ _ hseg _ am hx hb)
    hcode.bytesAt hlow (by rw [scanContext_seg_rex _ _ r hr, segAddr_segRexContext]; exact hread)
  simp only [scanContext_seg_rex _ _ r hr, segAddr_segRexContext] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_r64_m64_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegLoadPre p r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (r.prefixByte :: rex :: 0x3B :: am.modrm reg :: am.tail))
      (Effect.post (cmpR64M64SegEffect p (4 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpR64M64SegEffect_components]; simp [Component.Covers]) _)
    (cmp_r64_m64_seg_effect_step p r base rex hrex reg am hv hx hb)

theorem cmp_r64_m64_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (SegLoadPre p r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (r.prefixByte :: encodeCmpR64M64 dst am))
      (Effect.post (cmpR64M64SegEffect p (4 + am.tail.length) base (dst.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := cmp_r64_m64_seg_triple_of_bytes p r base _ hrex (regLow dst) am hv hx hb
  rwa [hr, gprNumber_reg] at this

attribute [x86_compose] cmpR64M64SegEffect

@[x86_local] theorem cmpR64M64SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} :
    Effect.Local (cmpR64M64SegEffect p len base dst am) := by
  effect_local [cmpR64M64SegEffect]

def cmpR32M32SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (.ofStatusFlags (cmpSpec a b)) }

@[simp] theorem cmpR32M32SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (cmpR32M32SegEffect p len base dst am s).components =
      [.flags, .rip] := rfl

def cmpR16M16SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  let b := (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (.ofStatusFlags (cmpSpec a b)) }

@[simp] theorem cmpR16M16SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (cmpR16M16SegEffect p len base dst am s).components =
      [.flags, .rip] := rfl

theorem cmp_r32_m32_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (SegLoadPre p r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: 0x3B :: am.modrm reg :: am.tail))
      (cmpR32M32SegEffect p (3 + am.tail.length) base (gprNumber 0 0 reg) am) := by
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
  have hstep := cmp_r_m_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_r32_m32_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SegLoadPre p r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: 0x3B :: am.modrm reg :: am.tail))
      (Effect.post (cmpR32M32SegEffect p (3 + am.tail.length) base (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpR32M32SegEffect_components]; simp [Component.Covers]) _)
    (cmp_r32_m32_seg_effect_step p r base reg am hv hx hb)

theorem cmp_r32_m32_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegLoadPre p r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: rex :: 0x3B :: am.modrm reg :: am.tail))
      (cmpR32M32SegEffect p (4 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
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
  have hstep := cmp_r_m_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_r32_m32_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegLoadPre p r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: rex :: 0x3B :: am.modrm reg :: am.tail))
      (Effect.post (cmpR32M32SegEffect p (4 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpR32M32SegEffect_components]; simp [Component.Covers]) _)
    (cmp_r32_m32_rex_seg_effect_step p r base rex hrex reg am hv hx hb)

theorem cmp_r16_m16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (SegLoadPre p r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: 0x3B :: am.modrm reg :: am.tail))
      (cmpR16M16SegEffect p (4 + am.tail.length) base (gprNumber 0 0 reg) am) := by
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
  have hstep := cmp_r16_m16_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_r16_m16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SegLoadPre p r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: 0x3B :: am.modrm reg :: am.tail))
      (Effect.post (cmpR16M16SegEffect p (4 + am.tail.length) base (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpR16M16SegEffect_components]; simp [Component.Covers]) _)
    (cmp_r16_m16_seg_effect_step p r base reg am hv hx hb)

theorem cmp_r16_m16_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegLoadPre p r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x3B :: am.modrm reg :: am.tail))
      (cmpR16M16SegEffect p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
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
  have hstep := cmp_r16_m16_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_r16_m16_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegLoadPre p r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x3B :: am.modrm reg :: am.tail))
      (Effect.post (cmpR16M16SegEffect p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpR16M16SegEffect_components]; simp [Component.Covers]) _)
    (cmp_r16_m16_rex_seg_effect_step p r base rex hrex reg am hv hx hb)

theorem cmp_r32_m32_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (SegLoadPre p r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeCmpR32M32 dst am).length)) 4)
      (codeRange p (r.prefixByte :: encodeCmpR32M32 dst am))
      (Effect.post (cmpR32M32SegEffect p (r.prefixByte :: encodeCmpR32M32 dst am).length base (dst.setWidth 5) am)) := by
  unfold encodeCmpR32M32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := cmp_r32_m32_seg_triple_of_bytes p r base (regLow dst) am hv hx hb
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := cmp_r32_m32_rex_seg_triple_of_bytes p r base _ hrex (regLow dst) am hv
      hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem cmp_r16_m16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (SegLoadPre p r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeCmpR16M16 dst am).length)) 2)
      (codeRange p (r.prefixByte :: encodeCmpR16M16 dst am))
      (Effect.post (cmpR16M16SegEffect p (r.prefixByte :: encodeCmpR16M16 dst am).length base (dst.setWidth 5) am)) := by
  unfold encodeCmpR16M16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := cmp_r16_m16_seg_triple_of_bytes p r base (regLow dst) am hv hx hb
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := cmp_r16_m16_rex_seg_triple_of_bytes p r base _ hrex (regLow dst) am hv
      hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

attribute [x86_compose] cmpR32M32SegEffect

@[x86_local] theorem cmpR32M32SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} :
    Effect.Local (cmpR32M32SegEffect p len base dst am) := by
  effect_local [cmpR32M32SegEffect]

attribute [x86_compose] cmpR16M16SegEffect

@[x86_local] theorem cmpR16M16SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} :
    Effect.Local (cmpR16M16SegEffect p len base dst am) := by
  effect_local [cmpR16M16SegEffect]

def cmpR64M64A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (.ofStatusFlags (cmpSpec a b)) }

@[simp] theorem cmpR64M64A32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (cmpR64M64A32Effect p len dst am s).components = [.flags, .rip] := rfl

def cmpR32M32A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (.ofStatusFlags (cmpSpec a b)) }

@[simp] theorem cmpR32M32A32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (cmpR32M32A32Effect p len dst am s).components = [.flags, .rip] := rfl

def cmpR16M16A32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  let b := (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (.ofStatusFlags (cmpSpec a b)) }

@[simp] theorem cmpR16M16A32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (cmpR16M16A32Effect p len dst am s).components = [.flags, .rip] := rfl

theorem cmp_r64_m64_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (0x67 :: rex :: 0x3B :: am.modrm reg :: am.tail))
      (cmpR64M64A32Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
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
  have hstep := cmp_r_m_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_r64_m64_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (0x67 :: rex :: 0x3B :: am.modrm reg :: am.tail))
      (Effect.post (cmpR64M64A32Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpR64M64A32Effect_components]; simp [Component.Covers]) _)
    (cmp_r64_m64_a32_effect_step p rex hrex reg am hv hx hb)

theorem cmp_r32_m32_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (0x67 :: 0x3B :: am.modrm reg :: am.tail))
      (cmpR32M32A32Effect p (3 + am.tail.length) (gprNumber 0 0 reg) am) := by
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
  have hstep := cmp_r_m_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_r32_m32_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (0x67 :: 0x3B :: am.modrm reg :: am.tail))
      (Effect.post (cmpR32M32A32Effect p (3 + am.tail.length) (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpR32M32A32Effect_components]; simp [Component.Covers]) _)
    (cmp_r32_m32_a32_effect_step p reg am hv hx hb)

theorem cmp_r32_m32_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (0x67 :: rex :: 0x3B :: am.modrm reg :: am.tail))
      (cmpR32M32A32Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
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
  have hstep := cmp_r_m_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_r32_m32_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (0x67 :: rex :: 0x3B :: am.modrm reg :: am.tail))
      (Effect.post (cmpR32M32A32Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpR32M32A32Effect_components]; simp [Component.Covers]) _)
    (cmp_r32_m32_rex_a32_effect_step p rex hrex reg am hv hx hb)

theorem cmp_r16_m16_a32_effect_step [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: 0x3B :: am.modrm reg :: am.tail))
      (cmpR16M16A32Effect p (4 + am.tail.length) (gprNumber 0 0 reg) am) := by
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
  have hstep := cmp_r16_m16_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_r16_m16_a32_triple_of_bytes [Bindings] (p : BitVec 64) 
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: 0x3B :: am.modrm reg :: am.tail))
      (Effect.post (cmpR16M16A32Effect p (4 + am.tail.length) (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpR16M16A32Effect_components]; simp [Component.Covers]) _)
    (cmp_r16_m16_a32_effect_step p reg am hv hx hb)

theorem cmp_r16_m16_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x3B :: am.modrm reg :: am.tail))
      (cmpR16M16A32Effect p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
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
  have hstep := cmp_r16_m16_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_loadWriteFlagsOutputs h _ _ _ _,
    ⟨afterStep_loadWriteFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_loadWriteFlagsOutputs s _ _ _ _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_r16_m16_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x3B :: am.modrm reg :: am.tail))
      (Effect.post (cmpR16M16A32Effect p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpR16M16A32Effect_components]; simp [Component.Covers]) _)
    (cmp_r16_m16_rex_a32_effect_step p rex hrex reg am hv hx hb)

theorem cmp_r64_m64_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeCmpR64M64 dst am).length)) 8)
      (codeRange p (0x67 :: encodeCmpR64M64 dst am))
      (Effect.post (cmpR64M64A32Effect p (0x67 :: encodeCmpR64M64 dst am).length (dst.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := cmp_r64_m64_a32_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
  rw [hr, gprNumber_reg] at this
  unfold encodeCmpR64M64
  simp only [List.length_cons]
  rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem cmp_r32_m32_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeCmpR32M32 dst am).length)) 4)
      (codeRange p (0x67 :: encodeCmpR32M32 dst am))
      (Effect.post (cmpR32M32A32Effect p (0x67 :: encodeCmpR32M32 dst am).length (dst.setWidth 5) am)) := by
  unfold encodeCmpR32M32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := cmp_r32_m32_a32_triple_of_bytes p (regLow dst) am hv hx hb
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := cmp_r32_m32_rex_a32_triple_of_bytes p _ hrex (regLow dst) am hv hx
      hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem cmp_r16_m16_a32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (LoadPre p (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeCmpR16M16 dst am).length)) 2)
      (codeRange p (0x67 :: encodeCmpR16M16 dst am))
      (Effect.post (cmpR16M16A32Effect p (0x67 :: encodeCmpR16M16 dst am).length (dst.setWidth 5) am)) := by
  unfold encodeCmpR16M16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := cmp_r16_m16_a32_triple_of_bytes p (regLow dst) am hv hx hb
    rw [show gprNumber 0 0 (regLow dst) = dst.setWidth 5 by rw [← gprNumber_reg dst, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := cmp_r16_m16_rex_a32_triple_of_bytes p _ hrex (regLow dst) am hv hx
      hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

attribute [x86_compose] cmpR64M64A32Effect cmpR32M32A32Effect cmpR16M16A32Effect

@[x86_local] theorem cmpR64M64A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (cmpR64M64A32Effect p len dst am) := by
  effect_local [cmpR64M64A32Effect]

@[x86_local] theorem cmpR32M32A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (cmpR32M32A32Effect p len dst am) := by
  effect_local [cmpR32M32A32Effect]

@[x86_local] theorem cmpR16M16A32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (cmpR16M16A32Effect p len dst am) := by
  effect_local [cmpR16M16A32Effect]

end X86Proofs
