import X86Proofs.Instructions.Mov.Generated.M8R8.Step
import X86Proofs.Instructions.Mov.Generated.M8R8.Encode
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movM8R8Effect (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    RamState → Effect :=
  storeEffect p len (fun s => am.addr s (p + BitVec.ofNat 64 len))
    fun s => (Operand.reg src : Operand 8).read s

theorem mov_m8_r8_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (StorePre p (2 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 1)
      (codeRange p (0x88 :: am.modrm reg :: am.tail))
      (movM8R8Effect p (2 + am.tail.length) (gprNumber 0 0 reg)
        am) :=
  StepEffect.of_store (n := 8) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp; omega)
        simp only [List.length_cons] at this
        omega
      have hstep := mov_m8_r8_step s h [] (by simp)
        (by simp)
        (by rfl) (by rfl)
        (by rfl) reg am hv
        (by exact (AddrContext.legacy _ am hx hb).toSeg)
        (.inr (by exact gprNumber_low4 reg hreg))
        hcode.bytesAt hlow (by exact hw)
      dsimp only at hstep
      have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
          (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 reg =
          (gprNumber 0 0 reg) := rfl
      rw [hsrc] at hstep
      exact hstep

theorem mov_m8_r8_triple_of_bytes [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (StorePre p (2 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 1)
      (codeRange p (0x88 :: am.modrm reg :: am.tail))
      (Effect.post (movM8R8Effect p (2 + am.tail.length) (gprNumber 0 0 reg)
        am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m8_r8_effect_step p reg hreg am hv hx hb)

theorem mov_m8_r8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (StorePre p (3 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (rex :: 0x88 :: am.modrm reg :: am.tail))
      (movM8R8Effect p (3 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am) :=
  StepEffect.of_store (n := 8) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp; omega)
        simp only [List.length_cons] at this
        omega
      have hstep := mov_m8_r8_step s h [rex] (by simpa using hr.scanPrefix)
        (by simp)
        (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
        (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
        (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
        (.inl (by rw [scanContext_rex _ _ hr]; rfl))
        hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hw)
      simp only [scanContext_rex _ _ hr] at hstep
      have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
          (rexContext s.DS rex.toBitVec).rex_r3 reg =
          (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
      rw [hsrc] at hstep
      exact hstep

theorem mov_m8_r8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (StorePre p (3 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (rex :: 0x88 :: am.modrm reg :: am.tail))
      (Effect.post (movM8R8Effect p (3 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m8_r8_rex_effect_step p rex hr reg am hv hx hb)

theorem mov_m8_r8_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (StorePre p (encodeMovM8R8 src am).length
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeMovM8R8 src am).length)) 1)
      (codeRange p (encodeMovM8R8 src am))
      (Effect.post (movM8R8Effect p (encodeMovM8R8 src am).length (src.setWidth 5) am)) := by
  unfold encodeMovM8R8
  split
  · rename_i hc
    obtain ⟨hs, hx, hb⟩ := hc
    obtain ⟨hr, hl⟩ := low4_spec src hs
    have := mov_m8_r8_triple_of_bytes p (regLow src) hl am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 = 2 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := mov_m8_r8_rex_triple_of_bytes p _ hrex.rexPrefix (regLow src) am hv
      hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]

attribute [x86_compose] movM8R8Effect

@[x86_local] theorem movM8R8Effect_local {p : BitVec 64} {len : Nat}
    {src : BitVec 5} {am : AddrMode} :
    Effect.Local (movM8R8Effect p len src am) := by
  effect_local [movM8R8Effect, storeEffect]

def movM8R8SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (src : BitVec 5)
    (am : AddrMode) : RamState → Effect :=
  storeEffect p len (fun s => base + am.addr s (p + BitVec.ofNat 64 len))
    fun s => (Operand.reg src : Operand 8).read s

theorem mov_m8_r8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (SegStorePre p (3 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (r.prefixByte :: 0x88 :: am.modrm reg :: am.tail))
      (movM8R8SegEffect p (3 + am.tail.length) base (gprNumber 0 0 reg)
        am) :=
  StepEffect.of_store_pre (n := 8) (by decide) (by decide) _ _ (fun _ hs => hs.store)
    fun s h hcode hpre => by
      obtain ⟨⟨hp, hw, _⟩, hseg, hbase⟩ := hpre
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
      have hstep := mov_m8_r8_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp))
        (by simp)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) reg am hv
        (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
        (.inr (by rw [hsc]; exact gprNumber_low4 reg hreg))
        hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hw)
      simp only [hsc, segAddr_withSeg] at hstep
      have hsrc : gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r4
          (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
          (gprNumber 0 0 reg) := rfl
      rw [hsrc] at hstep
      exact hstep

theorem mov_m8_r8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SegStorePre p (3 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (r.prefixByte :: 0x88 :: am.modrm reg :: am.tail))
      (Effect.post (movM8R8SegEffect p (3 + am.tail.length) base (gprNumber 0 0 reg)
        am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (mov_m8_r8_seg_effect_step p r base reg hreg am hv hx hb)

theorem mov_m8_r8_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegStorePre p (4 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (r.prefixByte :: rex :: 0x88 :: am.modrm reg :: am.tail))
      (movM8R8SegEffect p (4 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg)
        am) :=
  StepEffect.of_store_pre (n := 8) (by decide) (by decide) _ _ (fun _ hs => hs.store)
    fun s h hcode hpre => by
      obtain ⟨⟨hp, hw, _⟩, hseg, hbase⟩ := hpre
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
      have hstep := mov_m8_r8_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix))
        (by simp)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) reg am hv
        (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
        (.inl (by rw [hsc]; rfl))
        hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hw)
      simp only [hsc, segAddr_withSeg] at hstep
      have hsrc : gprNumber (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
          (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
          (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
      rw [hsrc] at hstep
      exact hstep

theorem mov_m8_r8_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegStorePre p (4 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (r.prefixByte :: rex :: 0x88 :: am.modrm reg :: am.tail))
      (Effect.post (movM8R8SegEffect p (4 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (mov_m8_r8_rex_seg_effect_step p r base rex hr reg am hv hx hb)

theorem mov_m8_r8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (SegStorePre p (r.prefixByte :: encodeMovM8R8 src am).length r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeMovM8R8 src am).length)) 1)
      (codeRange p (r.prefixByte :: encodeMovM8R8 src am))
      (Effect.post (movM8R8SegEffect p (r.prefixByte :: encodeMovM8R8 src am).length base (src.setWidth 5) am)) := by
  unfold encodeMovM8R8
  split
  · rename_i hc
    obtain ⟨hs, hx, hb⟩ := hc
    obtain ⟨hr, hl⟩ := low4_spec src hs
    have := mov_m8_r8_seg_triple_of_bytes p r base (regLow src) hl am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := mov_m8_r8_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix (regLow src)
      am hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

attribute [x86_compose] movM8R8SegEffect

@[x86_local] theorem movM8R8SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {src : BitVec 5} {am : AddrMode} :
    Effect.Local (movM8R8SegEffect p len base src am) := by
  effect_local [movM8R8SegEffect, storeEffect]

def movM8R8NoRexEffect (p : BitVec 64) (len : Nat) (src : BitVec 3) (am : AddrMode) :
    RamState → Effect :=
  storeEffect p len (fun s => am.addr s (p + BitVec.ofNat 64 len))
    fun s => (Operand.byteReg src).read s

def movM8R8NoRexSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (src : BitVec 3)
    (am : AddrMode) : RamState → Effect :=
  storeEffect p len (fun s => base + am.addr s (p + BitVec.ofNat 64 len))
    fun s => (Operand.byteReg src).read s

def movM8R8NoRexA32Effect (p : BitVec 64) (len : Nat) (src : BitVec 3) (am : AddrMode) :
    RamState → Effect :=
  storeEffect p len (fun s => am.addr32 s (p + BitVec.ofNat 64 len))
    fun s => (Operand.byteReg src).read s

theorem mov_m8_r8_norex_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (StorePre p (2 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 1)
      (codeRange p (0x88 :: am.modrm reg :: am.tail))
      (movM8R8NoRexEffect p (2 + am.tail.length) reg am) :=
  StepEffect.of_store (n := 8) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp; omega)
        simp only [List.length_cons] at this
        omega
      have hstep := mov_m8_r8_gpr8_step s h [] (by simp)
        (by simp)
        (by rfl) (by rfl)
        (by rfl) reg am hv
        (by exact (AddrContext.legacy _ am hx hb).toSeg)
        hcode.bytesAt hlow (by exact hw)
      dsimp only at hstep
      have hsrc : Operand.gpr8 (gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
          (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 reg)
          (byteRex (scanContext s.DS (PrefixSegments.ofState s) [])) = Operand.byteReg reg := rfl
      rw [hsrc] at hstep
      exact hstep

theorem mov_m8_r8_norex_triple_of_bytes [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (StorePre p (2 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 1)
      (codeRange p (0x88 :: am.modrm reg :: am.tail))
      (Effect.post (movM8R8NoRexEffect p (2 + am.tail.length) reg am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m8_r8_norex_effect_step p reg am hv hx hb)

theorem mov_m8_r8_norex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (SegStorePre p (3 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (r.prefixByte :: 0x88 :: am.modrm reg :: am.tail))
      (movM8R8NoRexSegEffect p (3 + am.tail.length) base reg am) :=
  StepEffect.of_store_pre (n := 8) (by decide) (by decide) _ _ (fun _ hs => hs.store)
    fun s h hcode hpre => by
      obtain ⟨⟨hp, hw, _⟩, hseg, hbase⟩ := hpre
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
      have hstep := mov_m8_r8_gpr8_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp))
        (by simp)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) reg am hv
        (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
        hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hw)
      simp only [hsc, segAddr_withSeg] at hstep
      have hsrc : Operand.gpr8 (gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r4
          (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r3 reg)
          (byteRex (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)))) = Operand.byteReg reg := rfl
      rw [hsrc] at hstep
      exact hstep

theorem mov_m8_r8_norex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SegStorePre p (3 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (r.prefixByte :: 0x88 :: am.modrm reg :: am.tail))
      (Effect.post (movM8R8NoRexSegEffect p (3 + am.tail.length) base reg am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (mov_m8_r8_norex_seg_effect_step p r base reg am hv hx hb)

theorem mov_m8_r8_norex_a32_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (StorePre p (3 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (0x67 :: 0x88 :: am.modrm reg :: am.tail))
      (movM8R8NoRexA32Effect p (3 + am.tail.length) reg am) :=
  StepEffect.of_store (n := 8) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp; omega)
        simp only [List.length_cons] at this
        omega
      have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
          withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
        rw [scanContext_asz_cons]
      have hstep := mov_m8_r8_gpr8_a32_step s h [0x67] (scanPrefix_asz_cons (by simp))
        (by simp)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) reg am hv
        (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
        hcode.bytesAt hlow (by rw [hsc]; exact hw)
      simp only [hsc] at hstep
      have hsrc : Operand.gpr8 (gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r4
          (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r3 reg)
          (byteRex (withAsz (scanContext s.DS (PrefixSegments.ofState s) []))) = Operand.byteReg reg := rfl
      rw [hsrc] at hstep
      exact hstep

theorem mov_m8_r8_norex_a32_triple_of_bytes [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (StorePre p (3 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (0x67 :: 0x88 :: am.modrm reg :: am.tail))
      (Effect.post (movM8R8NoRexA32Effect p (3 + am.tail.length) reg am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m8_r8_norex_a32_effect_step p reg am hv hx hb)

theorem mov_m8_r8_norex_triple [Bindings] (p : BitVec 64) (src : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (StorePre p (2 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 1)
      (codeRange p (encodeMovM8R8NoRex src am))
      (Effect.post (movM8R8NoRexEffect p (2 + am.tail.length) src am)) :=
  mov_m8_r8_norex_triple_of_bytes p src am hv hx hb

theorem mov_m8_r8_norex_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SegStorePre p (3 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (r.prefixByte :: encodeMovM8R8NoRex src am))
      (Effect.post (movM8R8NoRexSegEffect p (3 + am.tail.length) base src am)) :=
  mov_m8_r8_norex_seg_triple_of_bytes p r base src am hv hx hb

theorem mov_m8_r8_norex_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (StorePre p (3 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (0x67 :: encodeMovM8R8NoRex src am))
      (Effect.post (movM8R8NoRexA32Effect p (3 + am.tail.length) src am)) :=
  mov_m8_r8_norex_a32_triple_of_bytes p src am hv hx hb

attribute [x86_compose] movM8R8NoRexEffect movM8R8NoRexSegEffect movM8R8NoRexA32Effect

@[x86_local] theorem movM8R8NoRexEffect_local {p : BitVec 64} {len : Nat} {src : BitVec 3}
    {am : AddrMode} : Effect.Local (movM8R8NoRexEffect p len src am) := by
  effect_local [movM8R8NoRexEffect, storeEffect]

@[x86_local] theorem movM8R8NoRexSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {src : BitVec 3} {am : AddrMode} : Effect.Local (movM8R8NoRexSegEffect p len base src am) := by
  effect_local [movM8R8NoRexSegEffect, storeEffect]

@[x86_local] theorem movM8R8NoRexA32Effect_local {p : BitVec 64} {len : Nat} {src : BitVec 3}
    {am : AddrMode} : Effect.Local (movM8R8NoRexA32Effect p len src am) := by
  effect_local [movM8R8NoRexA32Effect, storeEffect]

def movM8R8A32Effect (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    RamState → Effect :=
  storeEffect p len (fun s => am.addr32 s (p + BitVec.ofNat 64 len))
    fun s => (Operand.reg src : Operand 8).read s

theorem mov_m8_r8_a32_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (StorePre p (3 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (0x67 :: 0x88 :: am.modrm reg :: am.tail))
      (movM8R8A32Effect p (3 + am.tail.length) (gprNumber 0 0 reg)
        am) :=
  StepEffect.of_store (n := 8) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp; omega)
        simp only [List.length_cons] at this
        omega
      have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
          withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
        rw [scanContext_asz_cons]
      have hstep := mov_m8_r8_a32_step s h [0x67] (scanPrefix_asz_cons (by simp))
        (by simp)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) reg am hv
        (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
        (.inr (by rw [hsc]; exact gprNumber_low4 reg hreg))
        hcode.bytesAt hlow (by rw [hsc]; exact hw)
      simp only [hsc] at hstep
      have hsrc : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r4
          (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r3 reg =
          (gprNumber 0 0 reg) := rfl
      rw [hsrc] at hstep
      exact hstep

theorem mov_m8_r8_a32_triple_of_bytes [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (hreg : reg.toNat < 4) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (StorePre p (3 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) 1)
      (codeRange p (0x67 :: 0x88 :: am.modrm reg :: am.tail))
      (Effect.post (movM8R8A32Effect p (3 + am.tail.length) (gprNumber 0 0 reg)
        am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m8_r8_a32_effect_step p reg hreg am hv hx hb)

theorem mov_m8_r8_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (StorePre p (4 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (0x67 :: rex :: 0x88 :: am.modrm reg :: am.tail))
      (movM8R8A32Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am) :=
  StepEffect.of_store (n := 8) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp; omega)
        simp only [List.length_cons] at this
        omega
      have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
          withAsz (rexContext s.DS rex.toBitVec) := by
        rw [scanContext_asz_cons, scanContext_rex _ _ hr]
      have hstep := mov_m8_r8_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix))
        (by simp)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) reg am hv
        (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
        (.inl (by rw [hsc]; rfl))
        hcode.bytesAt hlow (by rw [hsc]; exact hw)
      simp only [hsc] at hstep
      have hsrc : gprNumber (withAsz (rexContext s.DS rex.toBitVec)).rex_r4
          (withAsz (rexContext s.DS rex.toBitVec)).rex_r3 reg =
          (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
      rw [hsrc] at hstep
      exact hstep

theorem mov_m8_r8_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (StorePre p (4 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 1)
      (codeRange p (0x67 :: rex :: 0x88 :: am.modrm reg :: am.tail))
      (Effect.post (movM8R8A32Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m8_r8_rex_a32_effect_step p rex hr reg am hv hx hb)

theorem mov_m8_r8_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (StorePre p (0x67 :: encodeMovM8R8 src am).length
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeMovM8R8 src am).length)) 1)
      (codeRange p (0x67 :: encodeMovM8R8 src am))
      (Effect.post (movM8R8A32Effect p (0x67 :: encodeMovM8R8 src am).length (src.setWidth 5) am)) := by
  unfold encodeMovM8R8
  split
  · rename_i hc
    obtain ⟨hs, hx, hb⟩ := hc
    obtain ⟨hr, hl⟩ := low4_spec src hs
    have := mov_m8_r8_a32_triple_of_bytes p (regLow src) hl am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := mov_m8_r8_rex_a32_triple_of_bytes p _ hrex.rexPrefix (regLow src)
      am hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

attribute [x86_compose] movM8R8A32Effect

@[x86_local] theorem movM8R8A32Effect_local {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} :
    Effect.Local (movM8R8A32Effect p len src am) := by
  effect_local [movM8R8A32Effect, storeEffect]

end X86Proofs
