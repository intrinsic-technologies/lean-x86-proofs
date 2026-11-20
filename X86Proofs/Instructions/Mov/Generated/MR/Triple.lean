import X86Proofs.Instructions.Mov.Generated.MR.Step
import X86Proofs.Instructions.Mov.Generated.MR.Encode
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movM32R32LowEffect (p : BitVec 64) (src : BitVec 5) (am : AddrMode) :
    RamState → Effect :=
  storeEffect p (2 + am.tail.length) (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length)))
    fun s => (Operand.reg src : Operand 32).read s

def movM16R16Effect (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    RamState → Effect :=
  storeEffect p len (fun s => am.addr s (p + BitVec.ofNat 64 len))
    fun s => (Operand.reg src : Operand 16).read s

theorem mov_m32_r32_low_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (StorePre p (2 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 4)
      (codeRange p (0x89 :: am.modrm reg :: am.tail))
      (movM32R32LowEffect p (gprNumber 0 0 reg)
        am) :=
  StepEffect.of_store (n := 32) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp; omega)
        simp only [List.length_cons] at this
        omega
      have hstep := mov_m_r_step s h [] (by simp)
        (by simp) 32 (.inr rfl)
        (by exact rfl)
        (by rfl) (by rfl)
        (by rfl) reg am hv
        (by exact (AddrContext.legacy _ am hx hb).toSeg)
        hcode.bytesAt hlow (by exact hw)
      dsimp only at hstep
      have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
          (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 reg =
          (gprNumber 0 0 reg) := rfl
      rw [hsrc] at hstep
      exact hstep

theorem mov_m32_r32_low_triple_of_bytes [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (StorePre p (2 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 4)
      (codeRange p (0x89 :: am.modrm reg :: am.tail))
      (Effect.post (movM32R32LowEffect p (gprNumber 0 0 reg)
        am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m32_r32_low_effect_step p reg am hv hx hb)

theorem mov_m16_r16_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (StorePre p (3 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 2)
      (codeRange p (0x66 :: 0x89 :: am.modrm reg :: am.tail))
      (movM16R16Effect p (3 + am.tail.length) (gprNumber 0 0 reg)
        am) :=
  StepEffect.of_store (n := 16) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp; omega)
        simp only [List.length_cons] at this
        omega
      have hstep := mov_m16_r16_step s h [0x66] (by simpa using scanPrefix_66)
        (by simp)
        (by exact rfl)
        (by rfl) (by rfl)
        (by rfl) reg am hv
        (by exact (AddrContext.osz _ am hx hb).toSeg)
        hcode.bytesAt hlow (by exact hw)
      dsimp only at hstep
      have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r4
          (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r3 reg =
          (gprNumber 0 0 reg) := rfl
      rw [hsrc] at hstep
      exact hstep

theorem mov_m16_r16_triple_of_bytes [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (StorePre p (3 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 2)
      (codeRange p (0x66 :: 0x89 :: am.modrm reg :: am.tail))
      (Effect.post (movM16R16Effect p (3 + am.tail.length) (gprNumber 0 0 reg)
        am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m16_r16_effect_step p reg am hv hx hb)

theorem mov_m16_r16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (StorePre p (4 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (0x66 :: rex :: 0x89 :: am.modrm reg :: am.tail))
      (movM16R16Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am) :=
  StepEffect.of_store (n := 16) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      have hr := hrex.rexPrefix
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp; omega)
        simp only [List.length_cons] at this
        omega
      have hstep := mov_m16_r16_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix])
        (by simp)
        (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
        (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
        (by rw [scanContext_66_rex _ _ hr]; rfl) reg am hv
        (by rw [scanContext_66_rex _ _ hr]; exact (AddrContext.oszRex _ _ am hx hb).toSeg)
        hcode.bytesAt hlow (by rw [scanContext_66_rex _ _ hr]; exact hw)
      simp only [scanContext_66_rex _ _ hr] at hstep
      have hsrc : gprNumber (oszRexContext s.DS rex.toBitVec).rex_r4
          (oszRexContext s.DS rex.toBitVec).rex_r3 reg =
          (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
      rw [hsrc] at hstep
      exact hstep

theorem mov_m16_r16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (StorePre p (4 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (0x66 :: rex :: 0x89 :: am.modrm reg :: am.tail))
      (Effect.post (movM16R16Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m16_r16_rex_effect_step p rex hrex reg am hv hx hb)

theorem mov_m16_r16_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (StorePre p (encodeMovM16R16 src am).length
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeMovM16R16 src am).length)) 2)
      (codeRange p (encodeMovM16R16 src am))
      (Effect.post (movM16R16Effect p (encodeMovM16R16 src am).length (src.setWidth 5) am)) := by
  unfold encodeMovM16R16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := mov_m16_r16_triple_of_bytes p (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := mov_m16_r16_rex_triple_of_bytes p _ hrex (regLow src) am hv
      hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

attribute [x86_compose] movM32R32LowEffect movM16R16Effect

@[x86_local] theorem movM32R32LowEffect_local {p : BitVec 64}
    {src : BitVec 5} {am : AddrMode} :
    Effect.Local (movM32R32LowEffect p src am) := by
  effect_local [movM32R32LowEffect, storeEffect]

@[x86_local] theorem movM16R16Effect_local {p : BitVec 64} {len : Nat}
    {src : BitVec 5} {am : AddrMode} :
    Effect.Local (movM16R16Effect p len src am) := by
  effect_local [movM16R16Effect, storeEffect]

def movM64R64SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (src : BitVec 5)
    (am : AddrMode) : RamState → Effect :=
  storeEffect p len (fun s => base + am.addr s (p + BitVec.ofNat 64 len))
    fun s => (Operand.reg src : Operand 64).read s

def movM32R32SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (src : BitVec 5)
    (am : AddrMode) : RamState → Effect :=
  storeEffect p len (fun s => base + am.addr s (p + BitVec.ofNat 64 len))
    fun s => (Operand.reg src : Operand 32).read s

theorem mov_m64_r64_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegStorePre p (4 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (r.prefixByte :: rex :: 0x89 :: am.modrm reg :: am.tail))
      (movM64R64SegEffect p (4 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg)
        am) :=
  StepEffect.of_store_pre (n := 64) (by decide) (by decide) _ _ (fun _ hs => hs.store)
    fun s h hcode hpre => by
      have hr := hrex.rexPrefix
      obtain ⟨⟨hp, hw, _⟩, hseg, hbase⟩ := hpre
      subst hp hbase
      have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp; omega)
        simp only [List.length_cons] at this
        omega
      have hstep := mov_m_r_step s h [r.prefixByte, rex] (by simp [r.scanPrefix, hr.scanPrefix])
        (by simp) 64 (.inl rfl)
        (by rw [scanContext_seg_rex _ _ r hr]; exact hrex.operand_size_seg _ _)
        (by rw [scanContext_seg_rex _ _ r hr]; rfl) (by rw [scanContext_seg_rex _ _ r hr]; rfl)
        (by rw [scanContext_seg_rex _ _ r hr]; rfl) reg am hv
        (by rw [scanContext_seg_rex _ _ r hr]; exact SegAddrContext.seg_rex _ _ hseg _ am hx hb)
        hcode.bytesAt hlow (by rw [scanContext_seg_rex _ _ r hr, segAddr_segRexContext]; exact hw)
      simp only [scanContext_seg_rex _ _ r hr, segAddr_segRexContext] at hstep
      have hsrc : gprNumber (segRexContext s.DS (r.select (PrefixSegments.ofState s)) rex.toBitVec).rex_r4
          (segRexContext s.DS (r.select (PrefixSegments.ofState s)) rex.toBitVec).rex_r3 reg =
          gprNumber 0 (rexR rex.toBitVec) reg := rfl
      rw [hsrc] at hstep
      exact hstep

theorem mov_m64_r64_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegStorePre p (4 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (r.prefixByte :: rex :: 0x89 :: am.modrm reg :: am.tail))
      (Effect.post (movM64R64SegEffect p (4 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (mov_m64_r64_seg_effect_step p r base rex hrex reg am hv hx hb)

theorem mov_m64_r64_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (SegStorePre p (4 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (r.prefixByte :: encodeMovM64R64 src am))
      (Effect.post (movM64R64SegEffect p (4 + am.tail.length) base (src.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := mov_m64_r64_seg_triple_of_bytes p r base _ hrex (regLow src) am hv hx hb
  rwa [hr, gprNumber_reg] at this

theorem mov_m32_r32_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (SegStorePre p (3 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: 0x89 :: am.modrm reg :: am.tail))
      (movM32R32SegEffect p (3 + am.tail.length) base (gprNumber 0 0 reg) am) :=
  StepEffect.of_store_pre (n := 32) (by decide) (by decide) _ _ (fun _ hs => hs.store)
    fun s h hcode hpre => by
      obtain ⟨⟨hp, hw, _⟩, hseg, hbase⟩ := hpre
      subst hp hbase
      have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp; omega)
        simp only [List.length_cons] at this
        omega
      have hstep := mov_m_r_step s h [r.prefixByte] (by simp [r.scanPrefix])
        (by simp) 32 (.inr rfl)
        (by rw [scanContext_seg _ _ r]; rfl)
        (by rw [scanContext_seg _ _ r]; rfl) (by rw [scanContext_seg _ _ r]; rfl)
        (by rw [scanContext_seg _ _ r]; rfl) reg am hv
        (by rw [scanContext_seg _ _ r]; exact SegAddrContext.seg_legacy _ _ hseg am hx hb)
        hcode.bytesAt hlow (by rw [scanContext_seg _ _ r, segAddr_segContext]; exact hw)
      simp only [scanContext_seg _ _ r, segAddr_segContext] at hstep
      have hsrc : gprNumber (segContext s.DS (r.select (PrefixSegments.ofState s))).rex_r4
          (segContext s.DS (r.select (PrefixSegments.ofState s))).rex_r3 reg = gprNumber 0 0 reg := rfl
      rw [hsrc] at hstep
      exact hstep

theorem mov_m32_r32_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SegStorePre p (3 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: 0x89 :: am.modrm reg :: am.tail))
      (Effect.post (movM32R32SegEffect p (3 + am.tail.length) base (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (mov_m32_r32_seg_effect_step p r base reg am hv hx hb)

attribute [x86_compose] movM64R64SegEffect movM32R32SegEffect

@[x86_local] theorem movM64R64SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {src : BitVec 5} {am : AddrMode} :
    Effect.Local (movM64R64SegEffect p len base src am) := by
  effect_local [movM64R64SegEffect, storeEffect]

@[x86_local] theorem movM32R32SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {src : BitVec 5} {am : AddrMode} :
    Effect.Local (movM32R32SegEffect p len base src am) := by
  effect_local [movM32R32SegEffect, storeEffect]

def movM16R16SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (src : BitVec 5)
    (am : AddrMode) : RamState → Effect :=
  storeEffect p len (fun s => base + am.addr s (p + BitVec.ofNat 64 len))
    fun s => (Operand.reg src : Operand 16).read s

theorem mov_m32_r32_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegStorePre p (4 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: rex :: 0x89 :: am.modrm reg :: am.tail))
      (movM32R32SegEffect p (4 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg)
        am) :=
  StepEffect.of_store_pre (n := 32) (by decide) (by decide) _ _ (fun _ hs => hs.store)
    fun s h hcode hpre => by
      have hr := hrex.rexPrefix
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
      have hstep := mov_m_r_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix))
        (by simp) 32 (.inr rfl)
        (by rw [hsc]; exact hrex.operand_size s.DS)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) reg am hv
        (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
        hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hw)
      simp only [hsc, segAddr_withSeg] at hstep
      have hsrc : gprNumber (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
          (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
          (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
      rw [hsrc] at hstep
      exact hstep

theorem mov_m32_r32_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegStorePre p (4 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (r.prefixByte :: rex :: 0x89 :: am.modrm reg :: am.tail))
      (Effect.post (movM32R32SegEffect p (4 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (mov_m32_r32_rex_seg_effect_step p r base rex hrex reg am hv hx hb)

theorem mov_m16_r16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (SegStorePre p (4 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: 0x89 :: am.modrm reg :: am.tail))
      (movM16R16SegEffect p (4 + am.tail.length) base (gprNumber 0 0 reg)
        am) :=
  StepEffect.of_store_pre (n := 16) (by decide) (by decide) _ _ (fun _ hs => hs.store)
    fun s h hcode hpre => by
      obtain ⟨⟨hp, hw, _⟩, hseg, hbase⟩ := hpre
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
      have hstep := mov_m16_r16_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66))
        (by simp)
        (by rw [hsc]; exact rfl)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) reg am hv
        (by rw [hsc]; exact (AddrContext.osz _ am hx hb).withSeg hseg)
        hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hw)
      simp only [hsc, segAddr_withSeg] at hstep
      have hsrc : gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s))).rex_r4
          (withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
          (gprNumber 0 0 reg) := rfl
      rw [hsrc] at hstep
      exact hstep

theorem mov_m16_r16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SegStorePre p (4 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: 0x89 :: am.modrm reg :: am.tail))
      (Effect.post (movM16R16SegEffect p (4 + am.tail.length) base (gprNumber 0 0 reg)
        am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (mov_m16_r16_seg_effect_step p r base reg am hv hx hb)

theorem mov_m16_r16_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegStorePre p (5 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x89 :: am.modrm reg :: am.tail))
      (movM16R16SegEffect p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg)
        am) :=
  StepEffect.of_store_pre (n := 16) (by decide) (by decide) _ _ (fun _ hs => hs.store)
    fun s h hcode hpre => by
      have hr := hrex.rexPrefix
      obtain ⟨⟨hp, hw, _⟩, hseg, hbase⟩ := hpre
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
      have hstep := mov_m16_r16_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix]))
        (by simp)
        (by rw [hsc]; exact hrex.operand_size_osz s.DS)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) reg am hv
        (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).withSeg hseg)
        hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hw)
      simp only [hsc, segAddr_withSeg] at hstep
      have hsrc : gprNumber (withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
          (withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
          (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
      rw [hsrc] at hstep
      exact hstep

theorem mov_m16_r16_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegStorePre p (5 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x89 :: am.modrm reg :: am.tail))
      (Effect.post (movM16R16SegEffect p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (mov_m16_r16_rex_seg_effect_step p r base rex hrex reg am hv hx hb)

theorem mov_m16_r16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (SegStorePre p (r.prefixByte :: encodeMovM16R16 src am).length r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeMovM16R16 src am).length)) 2)
      (codeRange p (r.prefixByte :: encodeMovM16R16 src am))
      (Effect.post (movM16R16SegEffect p (r.prefixByte :: encodeMovM16R16 src am).length base (src.setWidth 5) am)) := by
  unfold encodeMovM16R16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := mov_m16_r16_seg_triple_of_bytes p r base (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := mov_m16_r16_rex_seg_triple_of_bytes p r base _ hrex (regLow src)
      am hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

attribute [x86_compose] movM16R16SegEffect

@[x86_local] theorem movM16R16SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {src : BitVec 5} {am : AddrMode} :
    Effect.Local (movM16R16SegEffect p len base src am) := by
  effect_local [movM16R16SegEffect, storeEffect]

def movM64R64A32Effect (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    RamState → Effect :=
  storeEffect p len (fun s => am.addr32 s (p + BitVec.ofNat 64 len))
    fun s => (Operand.reg src : Operand 64).read s

def movM32R32A32Effect (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    RamState → Effect :=
  storeEffect p len (fun s => am.addr32 s (p + BitVec.ofNat 64 len))
    fun s => (Operand.reg src : Operand 32).read s

def movM16R16A32Effect (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    RamState → Effect :=
  storeEffect p len (fun s => am.addr32 s (p + BitVec.ofNat 64 len))
    fun s => (Operand.reg src : Operand 16).read s

theorem mov_m64_r64_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (StorePre p (4 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (0x67 :: rex :: 0x89 :: am.modrm reg :: am.tail))
      (movM64R64A32Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am) :=
  StepEffect.of_store (n := 64) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      have hr := hrex.rexPrefix
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
      have hstep := mov_m_r_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix))
        (by simp) 64 (.inl rfl)
        (by rw [hsc]; exact hrex.operand_size s.DS)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) reg am hv
        (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
        hcode.bytesAt hlow (by rw [hsc]; exact hw)
      simp only [hsc] at hstep
      have hsrc : gprNumber (withAsz (rexContext s.DS rex.toBitVec)).rex_r4
          (withAsz (rexContext s.DS rex.toBitVec)).rex_r3 reg =
          (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
      rw [hsrc] at hstep
      exact hstep

theorem mov_m64_r64_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (StorePre p (4 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 8)
      (codeRange p (0x67 :: rex :: 0x89 :: am.modrm reg :: am.tail))
      (Effect.post (movM64R64A32Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m64_r64_a32_effect_step p rex hrex reg am hv hx hb)

theorem mov_m32_r32_a32_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (StorePre p (3 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (0x67 :: 0x89 :: am.modrm reg :: am.tail))
      (movM32R32A32Effect p (3 + am.tail.length) (gprNumber 0 0 reg)
        am) :=
  StepEffect.of_store (n := 32) (by decide) (by decide) _ _
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
      have hstep := mov_m_r_a32_step s h [0x67] (scanPrefix_asz_cons (by simp))
        (by simp) 32 (.inr rfl)
        (by rw [hsc]; exact rfl)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) reg am hv
        (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
        hcode.bytesAt hlow (by rw [hsc]; exact hw)
      simp only [hsc] at hstep
      have hsrc : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r4
          (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r3 reg =
          (gprNumber 0 0 reg) := rfl
      rw [hsrc] at hstep
      exact hstep

theorem mov_m32_r32_a32_triple_of_bytes [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (StorePre p (3 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (0x67 :: 0x89 :: am.modrm reg :: am.tail))
      (Effect.post (movM32R32A32Effect p (3 + am.tail.length) (gprNumber 0 0 reg)
        am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m32_r32_a32_effect_step p reg am hv hx hb)

theorem mov_m32_r32_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (StorePre p (4 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (0x67 :: rex :: 0x89 :: am.modrm reg :: am.tail))
      (movM32R32A32Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am) :=
  StepEffect.of_store (n := 32) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      have hr := hrex.rexPrefix
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
      have hstep := mov_m_r_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix))
        (by simp) 32 (.inr rfl)
        (by rw [hsc]; exact hrex.operand_size s.DS)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) reg am hv
        (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
        hcode.bytesAt hlow (by rw [hsc]; exact hw)
      simp only [hsc] at hstep
      have hsrc : gprNumber (withAsz (rexContext s.DS rex.toBitVec)).rex_r4
          (withAsz (rexContext s.DS rex.toBitVec)).rex_r3 reg =
          (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
      rw [hsrc] at hstep
      exact hstep

theorem mov_m32_r32_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (StorePre p (4 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (0x67 :: rex :: 0x89 :: am.modrm reg :: am.tail))
      (Effect.post (movM32R32A32Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m32_r32_rex_a32_effect_step p rex hrex reg am hv hx hb)

theorem mov_m16_r16_a32_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (StorePre p (4 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: 0x89 :: am.modrm reg :: am.tail))
      (movM16R16A32Effect p (4 + am.tail.length) (gprNumber 0 0 reg)
        am) :=
  StepEffect.of_store (n := 16) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp; omega)
        simp only [List.length_cons] at this
        omega
      have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66] =
          withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66]) := by
        rw [scanContext_asz_cons]
      have hstep := mov_m16_r16_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66))
        (by simp)
        (by rw [hsc]; exact rfl)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) reg am hv
        (by rw [hsc]; exact (AddrContext.osz _ am hx hb).toSeg.withAsz)
        hcode.bytesAt hlow (by rw [hsc]; exact hw)
      simp only [hsc] at hstep
      have hsrc : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66])).rex_r4
          (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66])).rex_r3 reg =
          (gprNumber 0 0 reg) := rfl
      rw [hsrc] at hstep
      exact hstep

theorem mov_m16_r16_a32_triple_of_bytes [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (StorePre p (4 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: 0x89 :: am.modrm reg :: am.tail))
      (Effect.post (movM16R16A32Effect p (4 + am.tail.length) (gprNumber 0 0 reg)
        am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m16_r16_a32_effect_step p reg am hv hx hb)

theorem mov_m16_r16_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (StorePre p (5 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x89 :: am.modrm reg :: am.tail))
      (movM16R16A32Effect p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am) :=
  StepEffect.of_store (n := 16) (by decide) (by decide) _ _
    fun s h hcode hpre => by
      have hr := hrex.rexPrefix
      obtain ⟨hp, hw, _⟩ := hpre
      subst hp
      have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp; omega)
        simp only [List.length_cons] at this
        omega
      have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66, rex] =
          withAsz (oszRexContext s.DS rex.toBitVec) := by
        rw [scanContext_asz_cons, scanContext_66_rex _ _ hr]
      have hstep := mov_m16_r16_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix]))
        (by simp)
        (by rw [hsc]; exact hrex.operand_size_osz s.DS)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl)
        (by rw [hsc]; rfl) reg am hv
        (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg.withAsz)
        hcode.bytesAt hlow (by rw [hsc]; exact hw)
      simp only [hsc] at hstep
      have hsrc : gprNumber (withAsz (oszRexContext s.DS rex.toBitVec)).rex_r4
          (withAsz (oszRexContext s.DS rex.toBitVec)).rex_r3 reg =
          (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
      rw [hsrc] at hstep
      exact hstep

theorem mov_m16_r16_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (StorePre p (5 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 2)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x89 :: am.modrm reg :: am.tail))
      (Effect.post (movM16R16A32Effect p (5 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre)
    (mov_m16_r16_rex_a32_effect_step p rex hrex reg am hv hx hb)

theorem mov_m64_r64_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (StorePre p (0x67 :: encodeMovM64R64 src am).length
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeMovM64R64 src am).length)) 8)
      (codeRange p (0x67 :: encodeMovM64R64 src am))
      (Effect.post (movM64R64A32Effect p (0x67 :: encodeMovM64R64 src am).length (src.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := mov_m64_r64_a32_triple_of_bytes p _ hrex (regLow src) am hv hx hb
  rw [hr, gprNumber_reg] at this
  unfold encodeMovM64R64
  simp only [List.length_cons]
  rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem mov_m32_r32_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (StorePre p (0x67 :: encodeMovM32R32 src am).length
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeMovM32R32 src am).length)) 4)
      (codeRange p (0x67 :: encodeMovM32R32 src am))
      (Effect.post (movM32R32A32Effect p (0x67 :: encodeMovM32R32 src am).length (src.setWidth 5) am)) := by
  unfold encodeMovM32R32
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := mov_m32_r32_a32_triple_of_bytes p (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := mov_m32_r32_rex_a32_triple_of_bytes p _ hrex (regLow src)
      am hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem mov_m16_r16_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (StorePre p (0x67 :: encodeMovM16R16 src am).length
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeMovM16R16 src am).length)) 2)
      (codeRange p (0x67 :: encodeMovM16R16 src am))
      (Effect.post (movM16R16A32Effect p (0x67 :: encodeMovM16R16 src am).length (src.setWidth 5) am)) := by
  unfold encodeMovM16R16
  split
  · rename_i hc
    obtain ⟨hr, hx, hb⟩ := hc
    have := mov_m16_r16_a32_triple_of_bytes p (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := mov_m16_r16_rex_a32_triple_of_bytes p _ hrex (regLow src)
      am hv hx hb
    rw [hr, gprNumber_reg] at this
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

attribute [x86_compose] movM64R64A32Effect movM32R32A32Effect movM16R16A32Effect

@[x86_local] theorem movM64R64A32Effect_local {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} :
    Effect.Local (movM64R64A32Effect p len src am) := by
  effect_local [movM64R64A32Effect, storeEffect]

@[x86_local] theorem movM32R32A32Effect_local {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} :
    Effect.Local (movM32R32A32Effect p len src am) := by
  effect_local [movM32R32A32Effect, storeEffect]

@[x86_local] theorem movM16R16A32Effect_local {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} :
    Effect.Local (movM16R16A32Effect p len src am) := by
  effect_local [movM16R16A32Effect, storeEffect]

end X86Proofs
