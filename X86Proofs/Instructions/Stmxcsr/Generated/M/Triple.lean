import X86Proofs.Instructions.Stmxcsr.Generated.M.Step
import X86Proofs.Instructions.Stmxcsr.Generated.M.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def stmxcsrM32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) : RamState → Effect :=
  storeEffect p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) fun s => stmxcsrSpec s.MXCSR

@[simp] theorem stmxcsrM32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (s : RamState) : (stmxcsrM32Effect p len am s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) 4, .rip] := by
  simp [stmxcsrM32Effect]

def stmxcsrM32SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode) :
    RamState → Effect :=
  storeEffect p len (fun s => base + am.addr s (p + BitVec.ofNat 64 len))
    fun s => stmxcsrSpec s.MXCSR

@[simp] theorem stmxcsrM32SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (am : AddrMode) (s : RamState) :
    (stmxcsrM32SegEffect p len base am s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) 4, .rip] := by
  simp [stmxcsrM32SegEffect]

def stmxcsrM32A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) : RamState → Effect :=
  storeEffect p len (fun s => am.addr32 s (p + BitVec.ofNat 64 len)) fun s => stmxcsrSpec s.MXCSR

@[simp] theorem stmxcsrM32A32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (s : RamState) : (stmxcsrM32A32Effect p len am s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) 4, .rip] := by
  simp [stmxcsrM32A32Effect]

theorem stmxcsr_m32_effect_step [Bindings] (p : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (SseStoreNPre p (3 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (0x0F :: 0xAE :: am.modrm 3 :: am.tail))
      (stmxcsrM32Effect p (3 + am.tail.length) am) := by
  refine StepEffect.of_store_pre (n := 32) (by decide) (by decide) _ _
    (fun _ hpre => hpre.store) fun s h hcode hpre => ?_
  have hp := hpre.store.rip
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := stmxcsr_m32_step s h hpre.sse []
    (by simp) (by simp)
    rfl rfl rfl
    rfl rfl
    am hv (AddrContext.legacy _ am hx hb).toSeg
    hcode.bytesAt hlow hpre.store.write
  dsimp only at hstep
  exact hstep

theorem stmxcsr_m32_triple_of_bytes [Bindings]
    (p : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (SseStoreNPre p (3 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (0x0F :: 0xAE :: am.modrm 3 :: am.tail))
      (Effect.post (stmxcsrM32Effect p (3 + am.tail.length) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (stmxcsr_m32_effect_step p am hv hx hb)

theorem stmxcsr_m32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (SseStoreNPre p (4 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (rex :: 0x0F :: 0xAE :: am.modrm 3 :: am.tail))
      (stmxcsrM32Effect p (4 + am.tail.length) am) := by
  refine StepEffect.of_store_pre (n := 32) (by decide) (by decide) _ _
    (fun _ hpre => hpre.store) fun s h hcode hpre => ?_
  have hp := hpre.store.rip
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hc := scanContext_rex s.DS (PrefixSegments.ofState s) hr
  have hstep := stmxcsr_m32_step s h hpre.sse [rex]
    (by simpa using hr.scanPrefix) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; rfl) (by rw [hc]; rfl)
    am hv (by rw [hc]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [hc]; exact hpre.store.write)
  simp only [hc] at hstep
  exact hstep

theorem stmxcsr_m32_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (SseStoreNPre p (4 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (rex :: 0x0F :: 0xAE :: am.modrm 3 :: am.tail))
      (Effect.post (stmxcsrM32Effect p (4 + am.tail.length) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (stmxcsr_m32_rex_effect_step p rex hr am hv hx hb)

theorem stmxcsr_m32_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (fun s => SseStoreNPre p (4 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0x0F :: 0xAE :: am.modrm 3 :: am.tail))
      (stmxcsrM32SegEffect p (4 + am.tail.length) base am) := by
  refine StepEffect.of_store_pre (n := 32) (by decide) (by decide) _ _
    (fun _ hpre => hpre.1.store) fun s h hcode hpre => ?_
  obtain ⟨hpre, hseg, hbase⟩ := hpre
  have hp := hpre.store.rip
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
  have hstep := stmxcsr_m32_step s h hpre.sse [r.prefixByte]
    (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.store.write)
  simp only [hsc, segAddr_withSeg] at hstep
  exact hstep

theorem stmxcsr_m32_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (fun s => SseStoreNPre p (4 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0x0F :: 0xAE :: am.modrm 3 :: am.tail))
      (Effect.post (stmxcsrM32SegEffect p (4 + am.tail.length) base am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.1.store)
    (stmxcsr_m32_seg_effect_step p r base am hv hx hb)

theorem stmxcsr_m32_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => SseStoreNPre p (5 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 4 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xAE :: am.modrm 3 :: am.tail))
      (stmxcsrM32SegEffect p (5 + am.tail.length) base am) := by
  refine StepEffect.of_store_pre (n := 32) (by decide) (by decide) _ _
    (fun _ hpre => hpre.1.store) fun s h hcode hpre => ?_
  obtain ⟨hpre, hseg, hbase⟩ := hpre
  have hp := hpre.store.rip
  subst hp hbase
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex s.DS (PrefixSegments.ofState s) hr]
  have hstep := stmxcsr_m32_step s h hpre.sse [r.prefixByte, rex]
    (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.store.write)
  simp only [hsc, segAddr_withSeg] at hstep
  exact hstep

theorem stmxcsr_m32_rex_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => SseStoreNPre p (5 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 4 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xAE :: am.modrm 3 :: am.tail))
      (Effect.post (stmxcsrM32SegEffect p (5 + am.tail.length) base am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.1.store)
    (stmxcsr_m32_rex_seg_effect_step p r base rex hr am hv hx hb)

theorem stmxcsr_m32_a32_effect_step [Bindings] (p : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (SseStoreNPre p (4 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (0x67 :: 0x0F :: 0xAE :: am.modrm 3 :: am.tail))
      (stmxcsrM32A32Effect p (4 + am.tail.length) am) := by
  refine StepEffect.of_store_pre (n := 32) (by decide) (by decide) _ _
    (fun _ hpre => hpre.store) fun s h hcode hpre => ?_
  have hp := hpre.store.rip
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := stmxcsr_m32_a32_step s h hpre.sse [0x67]
    (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.store.write)
  simp only [hsc] at hstep
  exact hstep

theorem stmxcsr_m32_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (SseStoreNPre p (4 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (0x67 :: 0x0F :: 0xAE :: am.modrm 3 :: am.tail))
      (Effect.post (stmxcsrM32A32Effect p (4 + am.tail.length) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (stmxcsr_m32_a32_effect_step p am hv hx hb)

theorem stmxcsr_m32_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (SseStoreNPre p (5 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xAE :: am.modrm 3 :: am.tail))
      (stmxcsrM32A32Effect p (5 + am.tail.length) am) := by
  refine StepEffect.of_store_pre (n := 32) (by decide) (by decide) _ _
    (fun _ hpre => hpre.store) fun s h hcode hpre => ?_
  have hp := hpre.store.rip
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex s.DS (PrefixSegments.ofState s) hr]
  have hstep := stmxcsr_m32_a32_step s h hpre.sse [0x67, rex]
    (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.store.write)
  simp only [hsc] at hstep
  exact hstep

theorem stmxcsr_m32_rex_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (SseStoreNPre p (5 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xAE :: am.modrm 3 :: am.tail))
      (Effect.post (stmxcsrM32A32Effect p (5 + am.tail.length) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (stmxcsr_m32_rex_a32_effect_step p rex hr am hv hx hb)

theorem stmxcsr_m32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple
      (SseStoreNPre p (encodeStmxcsrM32 am).length
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeStmxcsrM32 am).length)) 4)
      (codeRange p (encodeStmxcsrM32 am))
      (Effect.post (stmxcsrM32Effect p (encodeStmxcsrM32 am).length am)) := by
  unfold encodeStmxcsrM32
  rcases encodeSseMem_spec 0xAE 3 am with ⟨hbytes, hx, hb, -⟩ | hbytes
  · have hl : (0x0F :: 0xAE :: am.modrm (regLow 3) :: am.tail :
        List UInt8).length = 3 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact stmxcsr_m32_triple_of_bytes p am hv hx hb
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 3
    have hl : (am.rexByte false 3 :: 0x0F :: 0xAE :: am.modrm (regLow 3) ::
        am.tail).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact stmxcsr_m32_rex_triple_of_bytes p _ hrex.rexPrefix am hv hx hb

theorem stmxcsr_m32_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple
      (SseStoreNPre p (0x67 :: encodeStmxcsrM32 am).length
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeStmxcsrM32 am).length)) 4)
      (codeRange p (0x67 :: encodeStmxcsrM32 am))
      (Effect.post (stmxcsrM32A32Effect p (0x67 :: encodeStmxcsrM32 am).length am)) := by
  unfold encodeStmxcsrM32
  rcases encodeSseMem_spec 0xAE 3 am with ⟨hbytes, hx, hb, -⟩ | hbytes
  · have hl : (0x67 :: 0x0F :: 0xAE :: am.modrm (regLow 3) :: am.tail :
        List UInt8).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact stmxcsr_m32_a32_triple_of_bytes p am hv hx hb
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 3
    have hl : (0x67 :: am.rexByte false 3 :: 0x0F :: 0xAE :: am.modrm (regLow 3) ::
        am.tail).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact stmxcsr_m32_rex_a32_triple_of_bytes p _ hrex.rexPrefix am hv hx hb

theorem stmxcsr_m32_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) :
    Triple
      (fun s => SseStoreNPre p (r.prefixByte :: encodeStmxcsrM32 am).length
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodeStmxcsrM32 am).length)) 4 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: encodeStmxcsrM32 am))
      (Effect.post (stmxcsrM32SegEffect p (r.prefixByte :: encodeStmxcsrM32 am).length base am)) := by
  unfold encodeStmxcsrM32
  rcases encodeSseMem_spec 0xAE 3 am with ⟨hbytes, hx, hb, -⟩ | hbytes
  · have hl : (r.prefixByte :: 0x0F :: 0xAE :: am.modrm (regLow 3) ::
        am.tail : List UInt8).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact stmxcsr_m32_seg_triple_of_bytes p r base am hv hx hb
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 3
    have hl : (r.prefixByte :: am.rexByte false 3 :: 0x0F :: 0xAE ::
        am.modrm (regLow 3) :: am.tail).length = 5 + am.tail.length := by
      simp; omega
    rw [hbytes, hl]
    exact stmxcsr_m32_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix am hv hx hb

attribute [x86_compose] stmxcsrM32Effect

@[x86_local] theorem stmxcsrM32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (stmxcsrM32Effect p len am) := by
  effect_local [stmxcsrM32Effect, storeEffect]

attribute [x86_compose] stmxcsrM32SegEffect

@[x86_local] theorem stmxcsrM32SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} :
    Effect.Local (stmxcsrM32SegEffect p len base am) := by
  effect_local [stmxcsrM32SegEffect, storeEffect]

attribute [x86_compose] stmxcsrM32A32Effect

@[x86_local] theorem stmxcsrM32A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (stmxcsrM32A32Effect p len am) := by
  effect_local [stmxcsrM32A32Effect, storeEffect]

end X86Proofs
