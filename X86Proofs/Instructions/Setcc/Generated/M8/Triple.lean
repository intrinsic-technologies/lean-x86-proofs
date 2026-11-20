import X86Proofs.Instructions.Setcc.Generated.M8.Step
import X86Proofs.Instructions.Setcc.Generated.M8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def setccM8Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Bool) : RamState → Effect :=
  storeEffect p len (fun s => am.addr s (p + BitVec.ofNat 64 len))
    fun _ => (if c then 1 else 0 : BitVec 8)

def setccM8SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode) (c : Bool) :
    RamState → Effect :=
  storeEffect p len (fun s => base + am.addr s (p + BitVec.ofNat 64 len))
    fun _ => (if c then 1 else 0 : BitVec 8)

def setccM8A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Bool) : RamState → Effect :=
  storeEffect p len (fun s => am.addr32 s (p + BitVec.ofNat 64 len))
    fun _ => (if c then 1 else 0 : BitVec 8)

theorem setcc_m8_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s =>
        StorePre p (3 + am.tail.length)
          (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x0F :: setccOpcode cc :: am.modrm reg :: am.tail))
      (setccM8Effect p (3 + am.tail.length) am c) := by
  refine StepEffect.of_store_pre (n := 8) (by decide) (by decide) _ _ (fun _ hs => hs.1)
    fun s h hcode ⟨⟨hp, hw, _⟩, hc⟩ => ?_
  subst hp hc
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := setcc_m8_step s h [] (by simp) (by simp)
    (by rfl) (by rfl)
    (by rfl) cc reg am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hw)
  exact hstep

theorem setcc_m8_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s =>
        StorePre p (3 + am.tail.length)
          (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x0F :: setccOpcode cc :: am.modrm reg :: am.tail))
      (Effect.post (setccM8Effect p (3 + am.tail.length) am c)) :=
  Triple.of_effect (fun _ hs => storeEffect_avoids (by simp; omega) _ _ hs.1)
    (setcc_m8_effect_step p cc reg am hv hx hb c)

theorem setcc_m8_rex_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s =>
        StorePre p (4 + am.tail.length)
          (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (rex :: 0x0F :: setccOpcode cc :: am.modrm reg :: am.tail))
      (setccM8Effect p (4 + am.tail.length) am c) := by
  refine StepEffect.of_store_pre (n := 8) (by decide) (by decide) _ _ (fun _ hs => hs.1)
    fun s h hcode ⟨⟨hp, hw, _⟩, hc⟩ => ?_
  subst hp hc
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := setcc_m8_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) cc reg am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hw)
  simp only [scanContext_rex _ _ hr] at hstep
  exact hstep

theorem setcc_m8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s =>
        StorePre p (4 + am.tail.length)
          (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (rex :: 0x0F :: setccOpcode cc :: am.modrm reg :: am.tail))
      (Effect.post (setccM8Effect p (4 + am.tail.length) am c)) :=
  Triple.of_effect (fun _ hs => storeEffect_avoids (by simp; omega) _ _ hs.1)
    (setcc_m8_rex_effect_step p cc rex hr reg am hv hx hb c)

theorem setcc_m8_seg_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (r : SegReg)
    (base : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s =>
        SegStorePre p (4 + am.tail.length) r base
          (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (r.prefixByte :: 0x0F :: setccOpcode cc :: am.modrm reg :: am.tail))
      (setccM8SegEffect p (4 + am.tail.length) base am c) := by
  refine StepEffect.of_store_pre (n := 8) (by decide) (by decide) _ _ (fun _ hs => hs.1.store)
    fun s h hcode ⟨⟨⟨hp, hw, _⟩, hseg, hbase⟩, hc⟩ => ?_
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
  have hstep := setcc_m8_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) cc reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hw)
  simp only [hsc, segAddr_withSeg] at hstep
  exact hstep

theorem setcc_m8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (r : SegReg)
    (base : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s =>
        SegStorePre p (4 + am.tail.length) r base
          (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (r.prefixByte :: 0x0F :: setccOpcode cc :: am.modrm reg :: am.tail))
      (Effect.post (setccM8SegEffect p (4 + am.tail.length) base am c)) :=
  Triple.of_effect (fun _ hs => storeEffect_avoids (by simp; omega) _ _ hs.1.store)
    (setcc_m8_seg_effect_step p cc r base reg am hv hx hb c)

theorem setcc_m8_rex_seg_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s =>
        SegStorePre p (5 + am.tail.length) r base
          (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 1 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: setccOpcode cc :: am.modrm reg :: am.tail))
      (setccM8SegEffect p (5 + am.tail.length) base am c) := by
  refine StepEffect.of_store_pre (n := 8) (by decide) (by decide) _ _ (fun _ hs => hs.1.store)
    fun s h hcode ⟨⟨⟨hp, hw, _⟩, hseg, hbase⟩, hc⟩ => ?_
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
  have hstep := setcc_m8_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) cc reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hw)
  simp only [hsc, segAddr_withSeg] at hstep
  exact hstep

theorem setcc_m8_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s =>
        SegStorePre p (5 + am.tail.length) r base
          (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 1 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: setccOpcode cc :: am.modrm reg :: am.tail))
      (Effect.post (setccM8SegEffect p (5 + am.tail.length) base am c)) :=
  Triple.of_effect (fun _ hs => storeEffect_avoids (by simp; omega) _ _ hs.1.store)
    (setcc_m8_rex_seg_effect_step p cc r base rex hr reg am hv hx hb c)

theorem setcc_m8_a32_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    StepEffect (fun s =>
        StorePre p (4 + am.tail.length)
          (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x67 :: 0x0F :: setccOpcode cc :: am.modrm reg :: am.tail))
      (setccM8A32Effect p (4 + am.tail.length) am c) := by
  refine StepEffect.of_store_pre (n := 8) (by decide) (by decide) _ _ (fun _ hs => hs.1)
    fun s h hcode ⟨⟨hp, hw, _⟩, hc⟩ => ?_
  subst hp hc
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := setcc_m8_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) cc reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hw)
  simp only [hsc] at hstep
  exact hstep

theorem setcc_m8_a32_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) (c : Bool) :
    Triple (fun s =>
        StorePre p (4 + am.tail.length)
          (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x67 :: 0x0F :: setccOpcode cc :: am.modrm reg :: am.tail))
      (Effect.post (setccM8A32Effect p (4 + am.tail.length) am c)) :=
  Triple.of_effect (fun _ hs => storeEffect_avoids (by simp; omega) _ _ hs.1)
    (setcc_m8_a32_effect_step p cc reg am hv hx hb c)

theorem setcc_m8_rex_a32_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    StepEffect (fun s =>
        StorePre p (5 + am.tail.length)
          (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 1 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x67 :: rex :: 0x0F :: setccOpcode cc :: am.modrm reg :: am.tail))
      (setccM8A32Effect p (5 + am.tail.length) am c) := by
  refine StepEffect.of_store_pre (n := 8) (by decide) (by decide) _ _ (fun _ hs => hs.1)
    fun s h hcode ⟨⟨hp, hw, _⟩, hc⟩ => ?_
  subst hp hc
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := setcc_m8_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) cc reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hw)
  simp only [hsc] at hstep
  exact hstep

theorem setcc_m8_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (cc : BitVec 4) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (c : Bool) :
    Triple (fun s =>
        StorePre p (5 + am.tail.length)
          (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 1 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x67 :: rex :: 0x0F :: setccOpcode cc :: am.modrm reg :: am.tail))
      (Effect.post (setccM8A32Effect p (5 + am.tail.length) am c)) :=
  Triple.of_effect (fun _ hs => storeEffect_avoids (by simp; omega) _ _ hs.1)
    (setcc_m8_rex_a32_effect_step p cc rex hr reg am hv hx hb c)

theorem setcc_m8_triple [Bindings] (p : BitVec 64) (cc : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (c : Bool) :
    Triple (fun s =>
        StorePre p (encodeSetccM8 cc am).length
          (fun s => am.addr s (p + BitVec.ofNat 64 (encodeSetccM8 cc am).length)) 1 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (encodeSetccM8 cc am))
      (Effect.post (setccM8Effect p (encodeSetccM8 cc am).length am c)) := by
  unfold encodeSetccM8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := setcc_m8_triple_of_bytes p cc 0 am hv hx hb c
    rwa [show (0x0F :: setccOpcode cc :: am.modrm 0 :: am.tail).length =
      3 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := setcc_m8_rex_triple_of_bytes p cc _ hrex.rexPrefix 0 am hv hx hb c
    rwa [show (am.rexByte false 0 :: 0x0F :: setccOpcode cc :: am.modrm 0 :: am.tail).length =
      4 + am.tail.length by simp; omega]

theorem setcc_m8_seg_triple [Bindings] (p : BitVec 64) (cc : BitVec 4) (r : SegReg)
    (base : BitVec 64) (am : AddrMode) (hv : am.Valid) (c : Bool) :
    Triple (fun s =>
        SegStorePre p (r.prefixByte :: encodeSetccM8 cc am).length r base
          (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeSetccM8 cc am).length)) 1 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (r.prefixByte :: encodeSetccM8 cc am))
      (Effect.post (setccM8SegEffect p (r.prefixByte :: encodeSetccM8 cc am).length base am
        c)) := by
  unfold encodeSetccM8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := setcc_m8_seg_triple_of_bytes p cc r base 0 am hv hx hb c
    rwa [show (r.prefixByte :: 0x0F :: setccOpcode cc :: am.modrm 0 :: am.tail).length =
      4 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := setcc_m8_rex_seg_triple_of_bytes p cc r base _ hrex.rexPrefix 0 am hv hx hb c
    rwa [show (r.prefixByte :: am.rexByte false 0 :: 0x0F :: setccOpcode cc :: am.modrm 0 ::
      am.tail).length = 5 + am.tail.length by simp; omega]

theorem setcc_m8_a32_triple [Bindings] (p : BitVec 64) (cc : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (c : Bool) :
    Triple (fun s =>
        StorePre p (0x67 :: encodeSetccM8 cc am).length
          (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeSetccM8 cc am).length)) 1 s ∧
        condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p (0x67 :: encodeSetccM8 cc am))
      (Effect.post (setccM8A32Effect p (0x67 :: encodeSetccM8 cc am).length am c)) := by
  unfold encodeSetccM8
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := setcc_m8_a32_triple_of_bytes p cc 0 am hv hx hb c
    rwa [show (0x67 :: 0x0F :: setccOpcode cc :: am.modrm 0 :: am.tail).length =
      4 + am.tail.length by simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := setcc_m8_rex_a32_triple_of_bytes p cc _ hrex.rexPrefix 0 am hv hx hb c
    rwa [show (0x67 :: am.rexByte false 0 :: 0x0F :: setccOpcode cc :: am.modrm 0 ::
      am.tail).length = 5 + am.tail.length by simp; omega]

attribute [x86_compose] setccM8Effect setccM8SegEffect setccM8A32Effect

@[x86_local] theorem setccM8Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} {c : Bool} :
    Effect.Local (setccM8Effect p len am c) := by
  effect_local [setccM8Effect, storeEffect]

@[x86_local] theorem setccM8SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {c : Bool} : Effect.Local (setccM8SegEffect p len base am c) := by
  effect_local [setccM8SegEffect, storeEffect]

@[x86_local] theorem setccM8A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode}
    {c : Bool} : Effect.Local (setccM8A32Effect p len am c) := by
  effect_local [setccM8A32Effect, storeEffect]

end X86Proofs
