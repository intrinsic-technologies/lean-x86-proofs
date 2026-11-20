
import X86Proofs.Instructions.Mov.Generated.MImm32C7.Step
import X86Proofs.Instructions.Mov.Generated.MImm32C7.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movM32Imm32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    RamState → Effect :=
  storeEffect p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) fun _ => imm

def movM32Imm32SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode)
    (imm : BitVec 32) : RamState → Effect :=
  storeEffect p len (fun s => base + am.addr s (p + BitVec.ofNat 64 len)) fun _ => imm

def movM32Imm32A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    RamState → Effect :=
  storeEffect p len (fun s => am.addr32 s (p + BitVec.ofNat 64 len)) fun _ => imm

theorem mov_m32_imm32_effect_step [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) :
    StepEffect (StorePre p (6 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 4)
      (codeRange p (0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (movM32Imm32Effect p (6 + am.tail.length) am imm) := by
  refine StepEffect.of_store (n := 32) (by decide) (by decide) _ _
    fun s h hcode ⟨hp, hw, _⟩ => ?_
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := mov_m32_imm32_step s h [] (by simp)
    (by simp) (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by exact hw)
  simp only [movSpec, BitVec.signExtend_eq] at hstep
  exact hstep

theorem mov_m32_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) :
    Triple (StorePre p (6 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (6 + am.tail.length))) 4)
      (codeRange p (0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (movM32Imm32Effect p (6 + am.tail.length) am imm)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m32_imm32_effect_step p am hv hx hb imm)

theorem mov_m32_imm32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    StepEffect (StorePre p (7 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (7 + am.tail.length))) 4)
      (codeRange p (rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (movM32Imm32Effect p (7 + am.tail.length) am imm) := by
  have hr := hrex.rexPrefix
  refine StepEffect.of_store (n := 32) (by decide) (by decide) _ _
    fun s h hcode ⟨hp, hw, _⟩ => ?_
  subst hp
  have hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := mov_m32_imm32_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp) (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg) imm
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hw)
  simp only [scanContext_rex _ _ hr, movSpec, BitVec.signExtend_eq] at hstep
  exact hstep

theorem mov_m32_imm32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    Triple (StorePre p (7 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (7 + am.tail.length))) 4)
      (codeRange p (rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (movM32Imm32Effect p (7 + am.tail.length) am imm)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m32_imm32_rex_effect_step p rex hrex am hv hx hb imm)

theorem mov_m32_imm32_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) :
    StepEffect (SegStorePre p (7 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (7 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (movM32Imm32SegEffect p (7 + am.tail.length) base am imm) := by
  refine StepEffect.of_store_pre (n := 32) (by decide) (by decide) _ _ (fun _ hs => hs.store)
    fun s h hcode ⟨⟨hp, hw, _⟩, hseg, hbase⟩ => ?_
  subst hp hbase
  have hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := mov_m32_imm32_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp))
    (by simp) (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hw)
  simp only [hsc, segAddr_withSeg, movSpec, BitVec.signExtend_eq] at hstep
  exact hstep

theorem mov_m32_imm32_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) :
    Triple (SegStorePre p (7 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (7 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (movM32Imm32SegEffect p (7 + am.tail.length) base am imm)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (mov_m32_imm32_seg_effect_step p r base am hv hx hb imm)

theorem mov_m32_imm32_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    StepEffect (SegStorePre p (8 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (8 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (movM32Imm32SegEffect p (8 + am.tail.length) base am imm) := by
  have hr := hrex.rexPrefix
  refine StepEffect.of_store_pre (n := 32) (by decide) (by decide) _ _ (fun _ hs => hs.store)
    fun s h hcode ⟨⟨hp, hw, _⟩, hseg, hbase⟩ => ?_
  subst hp hbase
  have hlow : s.RIP.toNat + (8 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := mov_m32_imm32_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix))
    (by simp) (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg) imm
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hw)
  simp only [hsc, segAddr_withSeg, movSpec, BitVec.signExtend_eq] at hstep
  exact hstep

theorem mov_m32_imm32_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    Triple (SegStorePre p (8 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (8 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (movM32Imm32SegEffect p (8 + am.tail.length) base am imm)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (mov_m32_imm32_rex_seg_effect_step p r base rex hrex am hv hx hb imm)

theorem mov_m32_imm32_a32_effect_step [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) :
    StepEffect (StorePre p (7 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (7 + am.tail.length))) 4)
      (codeRange p (0x67 :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (movM32Imm32A32Effect p (7 + am.tail.length) am imm) := by
  refine StepEffect.of_store (n := 32) (by decide) (by decide) _ _
    fun s h hcode ⟨hp, hw, _⟩ => ?_
  subst hp
  have hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := mov_m32_imm32_a32_step s h [0x67] (scanPrefix_asz_cons (by simp))
    (by simp) (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hw)
  simp only [hsc, movSpec, BitVec.signExtend_eq] at hstep
  exact hstep

theorem mov_m32_imm32_a32_triple_of_bytes [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 32) :
    Triple (StorePre p (7 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (7 + am.tail.length))) 4)
      (codeRange p (0x67 :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (movM32Imm32A32Effect p (7 + am.tail.length) am imm)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m32_imm32_a32_effect_step p am hv hx hb imm)

theorem mov_m32_imm32_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    StepEffect (StorePre p (8 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (8 + am.tail.length))) 4)
      (codeRange p (0x67 :: rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (movM32Imm32A32Effect p (8 + am.tail.length) am imm) := by
  have hr := hrex.rexPrefix
  refine StepEffect.of_store (n := 32) (by decide) (by decide) _ _
    fun s h hcode ⟨hp, hw, _⟩ => ?_
  subst hp
  have hlow : s.RIP.toNat + (8 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := mov_m32_imm32_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix))
    (by simp) (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz) imm
    hcode.bytesAt hlow (by rw [hsc]; exact hw)
  simp only [hsc, movSpec, BitVec.signExtend_eq] at hstep
  exact hstep

theorem mov_m32_imm32_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32) :
    Triple (StorePre p (8 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (8 + am.tail.length))) 4)
      (codeRange p (0x67 :: rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
      (Effect.post (movM32Imm32A32Effect p (8 + am.tail.length) am imm)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m32_imm32_rex_a32_effect_step p rex hrex am hv hx hb imm)

theorem mov_m32_imm32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 32) :
    Triple (StorePre p (encodeMovM32Imm32 am imm).length
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeMovM32Imm32 am imm).length)) 4)
      (codeRange p (encodeMovM32Imm32 am imm))
      (Effect.post (movM32Imm32Effect p (encodeMovM32Imm32 am imm).length am imm)) := by
  unfold encodeMovM32Imm32
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := mov_m32_imm32_triple_of_bytes p am hv hx hb imm
    rwa [show (0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)).length =
      6 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := mov_m32_imm32_rex_triple_of_bytes p _ hrex am hv hx hb imm
    rwa [show (am.rexByte false 0 :: 0xC7 :: am.modrm 0 ::
      (am.tail ++ immBytes 32 imm)).length = 7 + am.tail.length by simp; omega]

theorem mov_m32_imm32_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (imm : BitVec 32) :
    Triple (SegStorePre p (r.prefixByte :: encodeMovM32Imm32 am imm).length r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeMovM32Imm32 am imm).length)) 4)
      (codeRange p (r.prefixByte :: encodeMovM32Imm32 am imm))
      (Effect.post (movM32Imm32SegEffect p (r.prefixByte :: encodeMovM32Imm32 am imm).length base am imm)) := by
  unfold encodeMovM32Imm32
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := mov_m32_imm32_seg_triple_of_bytes p r base am hv hx hb imm
    rwa [show (r.prefixByte :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)).length =
      7 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := mov_m32_imm32_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb imm
    rwa [show (r.prefixByte :: am.rexByte false 0 :: 0xC7 :: am.modrm 0 ::
      (am.tail ++ immBytes 32 imm)).length = 8 + am.tail.length by simp; omega]

theorem mov_m32_imm32_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (imm : BitVec 32) :
    Triple (StorePre p (0x67 :: encodeMovM32Imm32 am imm).length
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeMovM32Imm32 am imm).length)) 4)
      (codeRange p (0x67 :: encodeMovM32Imm32 am imm))
      (Effect.post (movM32Imm32A32Effect p (0x67 :: encodeMovM32Imm32 am imm).length am imm)) := by
  unfold encodeMovM32Imm32
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := mov_m32_imm32_a32_triple_of_bytes p am hv hx hb imm
    rwa [show (0x67 :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)).length =
      7 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := mov_m32_imm32_rex_a32_triple_of_bytes p _ hrex am hv hx hb imm
    rwa [show (0x67 :: am.rexByte false 0 :: 0xC7 :: am.modrm 0 ::
      (am.tail ++ immBytes 32 imm)).length = 8 + am.tail.length by simp; omega]

attribute [x86_compose] movM32Imm32Effect movM32Imm32SegEffect movM32Imm32A32Effect

@[x86_local] theorem movM32Imm32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode}
    {imm : BitVec 32} :
    Effect.Local (movM32Imm32Effect p len am imm) := by
  effect_local [movM32Imm32Effect, storeEffect]

@[x86_local] theorem movM32Imm32SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {imm : BitVec 32} :
    Effect.Local (movM32Imm32SegEffect p len base am imm) := by
  effect_local [movM32Imm32SegEffect, storeEffect]

@[x86_local] theorem movM32Imm32A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode}
    {imm : BitVec 32} :
    Effect.Local (movM32Imm32A32Effect p len am imm) := by
  effect_local [movM32Imm32A32Effect, storeEffect]

end X86Proofs
