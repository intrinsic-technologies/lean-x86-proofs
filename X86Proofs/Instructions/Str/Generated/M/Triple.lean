import X86Proofs.Instructions.Str.Generated.M.Step
import X86Proofs.Instructions.Str.Generated.M.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def strM16Effect (p : BitVec 64) (len : Nat) (am : AddrMode)
    (v : BitVec 16) : RamState → Effect :=
  storeEffect p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) fun _ => strSpec 16 v

@[simp] theorem strM16Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (v : BitVec 16) (s : RamState) :
    (strM16Effect p len am v s).components = [.mem (am.addr s (p + BitVec.ofNat 64 len)) (16 / 8), .rip] := rfl

def strM16SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode)
    (v : BitVec 16) : RamState → Effect :=
  storeEffect p len (fun s => base + am.addr s (p + BitVec.ofNat 64 len)) fun _ => strSpec 16 v

@[simp] theorem strM16SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode)
    (v : BitVec 16) (s : RamState) :
    (strM16SegEffect p len base am v s).components = [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) (16 / 8), .rip] := rfl

def strM16A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode)
    (v : BitVec 16) : RamState → Effect :=
  storeEffect p len (fun s => am.addr32 s (p + BitVec.ofNat 64 len)) fun _ => strSpec 16 v

@[simp] theorem strM16A32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (v : BitVec 16) (s : RamState) :
    (strM16A32Effect p len am v s).components = [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) (16 / 8), .rip] := rfl

theorem str_m16_effect_step [Bindings] (p : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (v : BitVec 16) :
    StepEffect (fun s => StorePre p (3 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧ SysRegReadable s ∧ s.TR.selector = v)
      (codeRange p (0x0F :: 0x00 :: am.modrm 1 :: am.tail))
      (strM16Effect p (3 + am.tail.length) am v) :=
  StepEffect.of_store_pre (n := 16) (by decide) (by decide) _ _ (fun _ hs => hs.1)
    fun s h hcode hpre => by
      obtain ⟨⟨hp, hw, _⟩, hsys, hsel⟩ := hpre
      subst hp
      have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp; omega)
        simp only [List.length_cons] at this
        omega
      have hstep := str_m16_step s h []
        (by simp) (by simp)
        (by rfl) (by rfl) (by rfl) hsys am hv
        (by exact (AddrContext.legacy _ am hx hb).toSeg)
        hcode.bytesAt hlow (by exact hw)
      simp only [List.length_nil, Nat.zero_add] at hstep
      rw [hsel] at hstep
      exact hstep

theorem str_m16_triple_of_bytes [Bindings] (p : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (v : BitVec 16) :
    Triple (fun s => StorePre p (3 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧ SysRegReadable s ∧ s.TR.selector = v)
      (codeRange p (0x0F :: 0x00 :: am.modrm 1 :: am.tail))
      (Effect.post (strM16Effect p (3 + am.tail.length) am v)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.1)
    (str_m16_effect_step p am hv hx hb v)

theorem str_m16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (v : BitVec 16) :
    StepEffect (fun s => StorePre p (4 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧ SysRegReadable s ∧ s.TR.selector = v)
      (codeRange p (rex :: 0x0F :: 0x00 :: am.modrm 1 :: am.tail))
      (strM16Effect p (4 + am.tail.length) am v) :=
  StepEffect.of_store_pre (n := 16) (by decide) (by decide) _ _ (fun _ hs => hs.1)
    fun s h hcode hpre => by
      have hr := hrex.rexPrefix
      obtain ⟨⟨hp, hw, _⟩, hsys, hsel⟩ := hpre
      subst hp
      have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp; omega)
        simp only [List.length_cons] at this
        omega
      have hstep := str_m16_step s h [rex]
        (by simpa using hr.scanPrefix) (by simp)
        (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) hsys am hv
        (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
        hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hw)
      simp only [scanContext_rex _ _ hr] at hstep
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
      rw [hsel] at hstep
      exact hstep

theorem str_m16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (v : BitVec 16) :
    Triple (fun s => StorePre p (4 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧ SysRegReadable s ∧ s.TR.selector = v)
      (codeRange p (rex :: 0x0F :: 0x00 :: am.modrm 1 :: am.tail))
      (Effect.post (strM16Effect p (4 + am.tail.length) am v)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.1)
    (str_m16_rex_effect_step p rex hrex am hv hx hb v)

theorem str_m16_triple [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (v : BitVec 16) :
    Triple (fun s => StorePre p (encodeStrM16 am).length
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeStrM16 am).length)) 2 s ∧
        SysRegReadable s ∧ s.TR.selector = v)
      (codeRange p (encodeStrM16 am))
      (Effect.post (strM16Effect p (encodeStrM16 am).length am v)) := by
  unfold encodeStrM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := str_m16_triple_of_bytes p am hv hx hb v
    rwa [show (0x0F :: 0x00 :: am.modrm 1 :: am.tail).length = 3 + am.tail.length by
      simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := str_m16_rex_triple_of_bytes p _ hrex am hv hx hb v
    rwa [show (am.rexByte false 0 :: 0x0F :: 0x00 :: am.modrm 1 :: am.tail).length =
      4 + am.tail.length by simp; omega]

theorem str_m16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (v : BitVec 16) :
    StepEffect (fun s => SegStorePre p (4 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧ SysRegReadable s ∧ s.TR.selector = v)
      (codeRange p (r.prefixByte :: 0x0F :: 0x00 :: am.modrm 1 :: am.tail))
      (strM16SegEffect p (4 + am.tail.length) base am v) :=
  StepEffect.of_store_pre (n := 16) (by decide) (by decide) _ _ (fun _ hs => hs.1.store)
    fun s h hcode hpre => by
      obtain ⟨⟨⟨hp, hw, _⟩, hseg, hbase⟩, hsys, hsel⟩ := hpre
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
      have hstep := str_m16_step s h [r.prefixByte]
        (scanPrefix_seg_cons r (by simp)) (by simp)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) hsys am hv
        (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
        hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hw)
      simp only [hsc, segAddr_withSeg, List.length_cons, List.length_nil, Nat.zero_add,
        Nat.reduceAdd] at hstep
      rw [hsel] at hstep
      exact hstep

theorem str_m16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (v : BitVec 16) :
    Triple (fun s => SegStorePre p (4 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧ SysRegReadable s ∧ s.TR.selector = v)
      (codeRange p (r.prefixByte :: 0x0F :: 0x00 :: am.modrm 1 :: am.tail))
      (Effect.post (strM16SegEffect p (4 + am.tail.length) base am v)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.1.store)
    (str_m16_seg_effect_step p r base am hv hx hb v)

theorem str_m16_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (v : BitVec 16) :
    StepEffect (fun s => SegStorePre p (5 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2 s ∧ SysRegReadable s ∧ s.TR.selector = v)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0x00 :: am.modrm 1 :: am.tail))
      (strM16SegEffect p (5 + am.tail.length) base am v) :=
  StepEffect.of_store_pre (n := 16) (by decide) (by decide) _ _ (fun _ hs => hs.1.store)
    fun s h hcode hpre => by
      have hr := hrex.rexPrefix
      obtain ⟨⟨⟨hp, hw, _⟩, hseg, hbase⟩, hsys, hsel⟩ := hpre
      subst hp hbase
      have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp; omega)
        simp only [List.length_cons] at this
        omega
      have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
          withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
        rw [scanContext_seg_cons _ _ r [rex]
          (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil),
          scanContext_rex _ _ hr]
      have hstep := str_m16_step s h [r.prefixByte, rex]
        (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) hsys am hv
        (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
        hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hw)
      simp only [hsc, segAddr_withSeg, List.length_cons, List.length_nil, Nat.zero_add,
        Nat.reduceAdd] at hstep
      rw [hsel] at hstep
      exact hstep

theorem str_m16_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (v : BitVec 16) :
    Triple (fun s => SegStorePre p (5 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2 s ∧ SysRegReadable s ∧ s.TR.selector = v)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0x00 :: am.modrm 1 :: am.tail))
      (Effect.post (strM16SegEffect p (5 + am.tail.length) base am v)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.1.store)
    (str_m16_rex_seg_effect_step p r base rex hrex am hv hx hb v)

theorem str_m16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (v : BitVec 16) :
    Triple (fun s => SegStorePre p (r.prefixByte :: encodeStrM16 am).length r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeStrM16 am).length)) 2 s ∧
        SysRegReadable s ∧ s.TR.selector = v)
      (codeRange p (r.prefixByte :: encodeStrM16 am))
      (Effect.post (strM16SegEffect p (r.prefixByte :: encodeStrM16 am).length base am v)) := by
  unfold encodeStrM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := str_m16_seg_triple_of_bytes p r base am hv hx hb v
    rwa [show (r.prefixByte :: 0x0F :: 0x00 :: am.modrm 1 :: am.tail).length = 4 + am.tail.length by
      simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := str_m16_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb v
    rwa [show (r.prefixByte :: am.rexByte false 0 :: 0x0F :: 0x00 :: am.modrm 1 :: am.tail).length =
      5 + am.tail.length by simp; omega]

theorem str_m16_a32_effect_step [Bindings] (p : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (v : BitVec 16) :
    StepEffect (fun s => StorePre p (4 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧ SysRegReadable s ∧ s.TR.selector = v)
      (codeRange p (0x67 :: 0x0F :: 0x00 :: am.modrm 1 :: am.tail))
      (strM16A32Effect p (4 + am.tail.length) am v) :=
  StepEffect.of_store_pre (n := 16) (by decide) (by decide) _ _ (fun _ hs => hs.1)
    fun s h hcode hpre => by
      obtain ⟨⟨hp, hw, _⟩, hsys, hsel⟩ := hpre
      subst hp
      have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp; omega)
        simp only [List.length_cons] at this
        omega
      have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
          withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
        rw [scanContext_asz_cons]
      have hstep := str_m16_a32_step s h [0x67]
        (scanPrefix_asz_cons (by simp)) (by simp)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) hsys am hv
        (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
        hcode.bytesAt hlow (by rw [hsc]; exact hw)
      simp only [hsc] at hstep
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
      rw [hsel] at hstep
      exact hstep

theorem str_m16_a32_triple_of_bytes [Bindings] (p : BitVec 64) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (v : BitVec 16) :
    Triple (fun s => StorePre p (4 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧ SysRegReadable s ∧ s.TR.selector = v)
      (codeRange p (0x67 :: 0x0F :: 0x00 :: am.modrm 1 :: am.tail))
      (Effect.post (strM16A32Effect p (4 + am.tail.length) am v)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.1)
    (str_m16_a32_effect_step p am hv hx hb v)

theorem str_m16_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (v : BitVec 16) :
    StepEffect (fun s => StorePre p (5 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2 s ∧ SysRegReadable s ∧ s.TR.selector = v)
      (codeRange p (0x67 :: rex :: 0x0F :: 0x00 :: am.modrm 1 :: am.tail))
      (strM16A32Effect p (5 + am.tail.length) am v) :=
  StepEffect.of_store_pre (n := 16) (by decide) (by decide) _ _ (fun _ hs => hs.1)
    fun s h hcode hpre => by
      have hr := hrex.rexPrefix
      obtain ⟨⟨hp, hw, _⟩, hsys, hsel⟩ := hpre
      subst hp
      have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp; omega)
        simp only [List.length_cons] at this
        omega
      have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
          withAsz (rexContext s.DS rex.toBitVec) := by
        rw [scanContext_asz_cons, scanContext_rex _ _ hr]
      have hstep := str_m16_a32_step s h [0x67, rex]
        (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) hsys am hv
        (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
        hcode.bytesAt hlow (by rw [hsc]; exact hw)
      simp only [hsc] at hstep
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
      rw [hsel] at hstep
      exact hstep

theorem str_m16_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (v : BitVec 16) :
    Triple (fun s => StorePre p (5 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2 s ∧ SysRegReadable s ∧ s.TR.selector = v)
      (codeRange p (0x67 :: rex :: 0x0F :: 0x00 :: am.modrm 1 :: am.tail))
      (Effect.post (strM16A32Effect p (5 + am.tail.length) am v)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.1)
    (str_m16_rex_a32_effect_step p rex hrex am hv hx hb v)

theorem str_m16_a32_triple [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (v : BitVec 16) :
    Triple (fun s => StorePre p (0x67 :: encodeStrM16 am).length
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeStrM16 am).length)) 2 s ∧
        SysRegReadable s ∧ s.TR.selector = v)
      (codeRange p (0x67 :: encodeStrM16 am))
      (Effect.post (strM16A32Effect p (0x67 :: encodeStrM16 am).length am v)) := by
  unfold encodeStrM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := str_m16_a32_triple_of_bytes p am hv hx hb v
    rwa [show (0x67 :: 0x0F :: 0x00 :: am.modrm 1 :: am.tail).length = 4 + am.tail.length by
      simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := str_m16_rex_a32_triple_of_bytes p _ hrex am hv hx hb v
    rwa [show (0x67 :: am.rexByte false 0 :: 0x0F :: 0x00 :: am.modrm 1 :: am.tail).length =
      5 + am.tail.length by simp; omega]

attribute [x86_compose] strM16Effect strM16SegEffect strM16A32Effect

@[x86_local] theorem strM16Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode}
    {v : BitVec 16} :
    Effect.Local (strM16Effect p len am v) := by
  effect_local [strM16Effect, storeEffect]

@[x86_local] theorem strM16SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {v : BitVec 16} :
    Effect.Local (strM16SegEffect p len base am v) := by
  effect_local [strM16SegEffect, storeEffect]

@[x86_local] theorem strM16A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode}
    {v : BitVec 16} :
    Effect.Local (strM16A32Effect p len am v) := by
  effect_local [strM16A32Effect, storeEffect]

end X86Proofs
