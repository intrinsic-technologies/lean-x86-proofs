import X86Proofs.Instructions.Movnti.Generated.MR32.Step
import X86Proofs.Instructions.Movnti.Generated.MR32.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movntiM32R32Effect (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    RamState → Effect :=
  storeEffect p len (fun s => am.addr s (p + BitVec.ofNat 64 len))
    fun s => movSpec ((Operand.reg src : Operand 32).read s)

@[simp] theorem movntiM32R32Effect_components (p : BitVec 64) (len : Nat) (src : BitVec 5)
    (am : AddrMode) (s : RamState) : (movntiM32R32Effect p len src am s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) 4, .rip] := by
  simp [movntiM32R32Effect]

def movntiM32R32SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (src : BitVec 5)
    (am : AddrMode) : RamState → Effect :=
  storeEffect p len (fun s => base + am.addr s (p + BitVec.ofNat 64 len))
    fun s => movSpec ((Operand.reg src : Operand 32).read s)

@[simp] theorem movntiM32R32SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (src : BitVec 5) (am : AddrMode) (s : RamState) :
    (movntiM32R32SegEffect p len base src am s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) 4, .rip] := by
  simp [movntiM32R32SegEffect]

def movntiM32R32A32Effect (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    RamState → Effect :=
  storeEffect p len (fun s => am.addr32 s (p + BitVec.ofNat 64 len))
    fun s => movSpec ((Operand.reg src : Operand 32).read s)

@[simp] theorem movntiM32R32A32Effect_components (p : BitVec 64) (len : Nat) (src : BitVec 5)
    (am : AddrMode) (s : RamState) : (movntiM32R32A32Effect p len src am s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) 4, .rip] := by
  simp [movntiM32R32A32Effect]

theorem movnti_m32_r32_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (Sse2GprStorePre p (3 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (0x0F :: 0xC3 :: am.modrm reg :: am.tail))
      (movntiM32R32Effect p (3 + am.tail.length)
        (gprNumber 0 0 reg) am) := by
  refine StepEffect.of_store_pre (n := 32) (by decide) (by decide) _ _
    (fun _ hpre => hpre.store) fun s h hcode hpre => ?_
  have hp := hpre.store.rip
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := movnti_m32_r32_step s h hpre.sse2 []
    (by simp) (by simp)
    rfl rfl rfl
    rfl rfl rfl
    reg am hv (AddrContext.legacy _ am hx hb).toSeg
    hcode.bytesAt hlow hpre.store.write
  dsimp only at hstep
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 reg = (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  exact hstep

theorem movnti_m32_r32_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (Sse2GprStorePre p (3 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 4)
      (codeRange p (0x0F :: 0xC3 :: am.modrm reg :: am.tail))
      (Effect.post (movntiM32R32Effect p (3 + am.tail.length)
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (movnti_m32_r32_effect_step p reg am hv hx hb)

theorem movnti_m32_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (Sse2GprStorePre p (4 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (rex :: 0x0F :: 0xC3 :: am.modrm reg :: am.tail))
      (movntiM32R32Effect p (4 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  refine StepEffect.of_store_pre (n := 32) (by decide) (by decide) _ _
    (fun _ hpre => hpre.store) fun s h hcode hpre => ?_
  have hp := hpre.store.rip
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hc := scanContext_rex s.DS (PrefixSegments.ofState s) hr.rexPrefix
  have hstep := movnti_m32_r32_step s h hpre.sse2 [rex]
    (by simpa using hr.rexPrefix.scanPrefix) (by simp)
    (by rw [hc]; rfl) (by rw [hc]; rfl) (by rw [hc]; rfl)
    (by rw [hc]; exact hr.rex_w s.DS) (by rw [hc]; rfl) (by rw [hc]; rfl)
    reg am hv (by rw [hc]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [hc]; exact hpre.store.write)
  simp only [hc] at hstep
  have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  exact hstep

theorem movnti_m32_r32_rex_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (Sse2GprStorePre p (4 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (rex :: 0x0F :: 0xC3 :: am.modrm reg :: am.tail))
      (Effect.post (movntiM32R32Effect p (4 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (movnti_m32_r32_rex_effect_step p rex hr reg am hv hx hb)

theorem movnti_m32_r32_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (fun s => Sse2GprStorePre p (4 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0x0F :: 0xC3 :: am.modrm reg :: am.tail))
      (movntiM32R32SegEffect p (4 + am.tail.length) base
        (gprNumber 0 0 reg) am) := by
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
  have hstep := movnti_m32_r32_step s h hpre.sse2 [r.prefixByte]
    (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.store.write)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r3 reg = (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  exact hstep

theorem movnti_m32_r32_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (fun s => Sse2GprStorePre p (4 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) 4 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0x0F :: 0xC3 :: am.modrm reg :: am.tail))
      (Effect.post (movntiM32R32SegEffect p (4 + am.tail.length) base
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.1.store)
    (movnti_m32_r32_seg_effect_step p r base reg am hv hx hb)

theorem movnti_m32_r32_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (fun s => Sse2GprStorePre p (5 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 4 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xC3 :: am.modrm reg :: am.tail))
      (movntiM32R32SegEffect p (5 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
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
      (noSegPrefix_cons hr.rexPrefix.noSegPrefix noSegPrefix_nil), scanContext_rex s.DS (PrefixSegments.ofState s) hr.rexPrefix]
  have hstep := movnti_m32_r32_step s h hpre.sse2 [r.prefixByte, rex]
    (scanPrefix_seg_cons r (by simpa using hr.rexPrefix.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; exact hr.rex_w s.DS) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hpre.store.write)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  exact hstep

theorem movnti_m32_r32_rex_seg_triple_of_bytes [Bindings]
    (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (fun s => Sse2GprStorePre p (5 + am.tail.length)
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) 4 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xC3 :: am.modrm reg :: am.tail))
      (Effect.post (movntiM32R32SegEffect p (5 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.1.store)
    (movnti_m32_r32_rex_seg_effect_step p r base rex hr reg am hv hx hb)

theorem movnti_m32_r32_a32_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect
      (Sse2GprStorePre p (4 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (0x67 :: 0x0F :: 0xC3 :: am.modrm reg :: am.tail))
      (movntiM32R32A32Effect p (4 + am.tail.length)
        (gprNumber 0 0 reg) am) := by
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
  have hstep := movnti_m32_r32_a32_step s h hpre.sse2 [0x67]
    (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.store.write)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r4
      (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r3 reg = (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  exact hstep

theorem movnti_m32_r32_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple
      (Sse2GprStorePre p (4 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 4)
      (codeRange p (0x67 :: 0x0F :: 0xC3 :: am.modrm reg :: am.tail))
      (Effect.post (movntiM32R32A32Effect p (4 + am.tail.length)
        (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (movnti_m32_r32_a32_effect_step p reg am hv hx hb)

theorem movnti_m32_r32_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect
      (Sse2GprStorePre p (5 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xC3 :: am.modrm reg :: am.tail))
      (movntiM32R32A32Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
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
    rw [scanContext_asz_cons, scanContext_rex s.DS (PrefixSegments.ofState s) hr.rexPrefix]
  have hstep := movnti_m32_r32_a32_step s h hpre.sse2 [0x67, rex]
    (scanPrefix_asz_cons (by simpa using hr.rexPrefix.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; exact hr.rex_w s.DS) (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    reg am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hpre.store.write)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (rexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (rexContext s.DS rex.toBitVec)).rex_r3 reg = (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  exact hstep

theorem movnti_m32_r32_rex_a32_triple_of_bytes [Bindings]
    (p : BitVec 64) (rex : UInt8)
    (hr : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple
      (Sse2GprStorePre p (5 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (5 + am.tail.length))) 4)
      (codeRange p (0x67 :: rex :: 0x0F :: 0xC3 :: am.modrm reg :: am.tail))
      (Effect.post (movntiM32R32A32Effect p (5 + am.tail.length)
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.store)
    (movnti_m32_r32_rex_a32_effect_step p rex hr reg am hv hx hb)

theorem movnti_m32_r32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (Sse2GprStorePre p (encodeMovntiM32R32 src am).length
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeMovntiM32R32 src am).length)) 4)
      (codeRange p (encodeMovntiM32R32 src am))
      (Effect.post (movntiM32R32Effect p (encodeMovntiM32R32 src am).length
        (src.setWidth 5) am)) := by
  unfold encodeMovntiM32R32
  rcases encodeSseMem_spec 0xC3 src am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (0x0F :: 0xC3 :: am.modrm (regLow src) :: am.tail :
        List UInt8).length = 3 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact movnti_m32_r32_triple_of_bytes p (regLow src) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := movnti_m32_r32_rex_triple_of_bytes p _ hrex (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (am.rexByte false src :: 0x0F :: 0xC3 :: am.modrm (regLow src) ::
        am.tail).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact this

theorem movnti_m32_r32_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple
      (fun s => Sse2GprStorePre p (r.prefixByte :: encodeMovntiM32R32 src am).length
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (r.prefixByte :: encodeMovntiM32R32 src am).length)) 4 s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: encodeMovntiM32R32 src am))
      (Effect.post (movntiM32R32SegEffect p (r.prefixByte :: encodeMovntiM32R32 src am).length base
        (src.setWidth 5) am)) := by
  unfold encodeMovntiM32R32
  rcases encodeSseMem_spec 0xC3 src am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (r.prefixByte :: 0x0F :: 0xC3 :: am.modrm (regLow src) ::
        am.tail : List UInt8).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact movnti_m32_r32_seg_triple_of_bytes p r base (regLow src) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := movnti_m32_r32_rex_seg_triple_of_bytes p r base _
      hrex (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (r.prefixByte :: am.rexByte false src :: 0x0F :: 0xC3 ::
        am.modrm (regLow src) :: am.tail).length = 5 + am.tail.length := by
      simp; omega
    rw [hbytes, hl]
    exact this

attribute [x86_compose] movntiM32R32Effect

@[x86_local] theorem movntiM32R32Effect_local {p : BitVec 64} {len : Nat} {src : BitVec 5}
    {am : AddrMode} :
    Effect.Local (movntiM32R32Effect p len src am) := by
  effect_local [movntiM32R32Effect, storeEffect]

attribute [x86_compose] movntiM32R32SegEffect

@[x86_local] theorem movntiM32R32SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {src : BitVec 5} {am : AddrMode} :
    Effect.Local (movntiM32R32SegEffect p len base src am) := by
  effect_local [movntiM32R32SegEffect, storeEffect]

theorem movnti_m32_r32_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple
      (Sse2GprStorePre p (0x67 :: encodeMovntiM32R32 src am).length
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeMovntiM32R32 src am).length)) 4)
      (codeRange p (0x67 :: encodeMovntiM32R32 src am))
      (Effect.post (movntiM32R32A32Effect p (0x67 :: encodeMovntiM32R32 src am).length
        (src.setWidth 5) am)) := by
  unfold encodeMovntiM32R32
  rcases encodeSseMem_spec 0xC3 src am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (0x67 :: 0x0F :: 0xC3 :: am.modrm (regLow src) ::
        am.tail : List UInt8).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact movnti_m32_r32_a32_triple_of_bytes p (regLow src) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := movnti_m32_r32_rex_a32_triple_of_bytes p _
      hrex (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (0x67 :: am.rexByte false src :: 0x0F :: 0xC3 ::
        am.modrm (regLow src) :: am.tail).length = 5 + am.tail.length := by
      simp; omega
    rw [hbytes, hl]
    exact this

attribute [x86_compose] movntiM32R32A32Effect

@[x86_local] theorem movntiM32R32A32Effect_local {p : BitVec 64} {len : Nat}
    {src : BitVec 5} {am : AddrMode} :
    Effect.Local (movntiM32R32A32Effect p len src am) := by
  effect_local [movntiM32R32A32Effect, storeEffect]

end X86Proofs
