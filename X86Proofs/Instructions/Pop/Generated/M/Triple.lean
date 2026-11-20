import X86Proofs.Instructions.Pop.Generated.M.Step
import X86Proofs.Instructions.Pop.Generated.M.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def popM64Effect (p : BitVec 64) (len : Nat) (am : AddrMode) : RamState → Effect :=
  popMemEffect p len 64 am

def popM64SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode) :
    RamState → Effect :=
  popMemSegEffect p len 64 base am

def popM64A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) : RamState → Effect :=
  popMemA32Effect p len 64 am

theorem pop_m64_effect_step [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (PopMemPre p (2 + am.tail.length) 64 am)
      (codeRange p (0x8F :: am.modrm 0 :: am.tail))
      (popM64Effect p (2 + am.tail.length) am) := by
  refine StepEffect.of_popMem (by decide) (by decide) am fun s h hcode ⟨hpre, hread⟩ => ?_
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := pop_m64_step s h [] (by simp) (by simp)
    (by rfl) (by rfl)
    (by rfl) (by rfl)
    am hv (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow hread (by exact hpre.write)
  exact hstep

theorem pop_m64_triple_of_bytes [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (PopMemPre p (2 + am.tail.length) 64 am)
      (codeRange p (0x8F :: am.modrm 0 :: am.tail))
      (Effect.post (popM64Effect p (2 + am.tail.length) am)) :=
  Triple.of_effect (fun _ hpre => popMemEffect_avoids (by simp; omega) am hpre)
    (pop_m64_effect_step p am hv hx hb)

theorem pop_m64_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (PopMemPre p (3 + am.tail.length) 64 am)
      (codeRange p (rex :: 0x8F :: am.modrm 0 :: am.tail))
      (popM64Effect p (3 + am.tail.length) am) := by
  refine StepEffect.of_popMem (by decide) (by decide) am fun s h hcode ⟨hpre, hread⟩ => ?_
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := pop_m64_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    am hv (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow hread (by rw [scanContext_rex _ _ hr]; exact hpre.write)
  simp only [scanContext_rex _ _ hr] at hstep
  exact hstep

theorem pop_m64_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (PopMemPre p (3 + am.tail.length) 64 am)
      (codeRange p (rex :: 0x8F :: am.modrm 0 :: am.tail))
      (Effect.post (popM64Effect p (3 + am.tail.length) am)) :=
  Triple.of_effect (fun _ hpre => popMemEffect_avoids (by simp; omega) am hpre)
    (pop_m64_rex_effect_step p rex hr am hv hx hb)

theorem pop_m64_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (PopMemSegPre p (3 + am.tail.length) 64 r base am)
      (codeRange p (r.prefixByte :: 0x8F :: am.modrm 0 :: am.tail))
      (popM64SegEffect p (3 + am.tail.length) base am) := by
  refine StepEffect.of_popMemSeg (by decide) (by decide) r base am
    fun s h hcode hpre => ?_
  obtain ⟨⟨⟨hp, hw, -⟩, hseg, hbase⟩, hread⟩ := hpre
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
  have hstep := pop_m64_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow hread (by rw [hsc, segAddr_withSeg]; exact hw)
  simp only [hsc] at hstep
  exact hstep

theorem pop_m64_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (PopMemSegPre p (3 + am.tail.length) 64 r base am)
      (codeRange p (r.prefixByte :: 0x8F :: am.modrm 0 :: am.tail))
      (Effect.post (popM64SegEffect p (3 + am.tail.length) base am)) :=
  Triple.of_effect (fun _ hpre => popMemSegEffect_avoids (by simp; omega) am hpre)
    (pop_m64_seg_effect_step p r base am hv hx hb)

theorem pop_m64_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (PopMemSegPre p (4 + am.tail.length) 64 r base am)
      (codeRange p (r.prefixByte :: rex :: 0x8F :: am.modrm 0 :: am.tail))
      (popM64SegEffect p (4 + am.tail.length) base am) := by
  refine StepEffect.of_popMemSeg (by decide) (by decide) r base am
    fun s h hcode hpre => ?_
  obtain ⟨⟨⟨hp, hw, -⟩, hseg, hbase⟩, hread⟩ := hpre
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
  have hstep := pop_m64_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow hread (by rw [hsc, segAddr_withSeg]; exact hw)
  simp only [hsc] at hstep
  exact hstep

theorem pop_m64_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (PopMemSegPre p (4 + am.tail.length) 64 r base am)
      (codeRange p (r.prefixByte :: rex :: 0x8F :: am.modrm 0 :: am.tail))
      (Effect.post (popM64SegEffect p (4 + am.tail.length) base am)) :=
  Triple.of_effect (fun _ hpre => popMemSegEffect_avoids (by simp; omega) am hpre)
    (pop_m64_rex_seg_effect_step p r base rex hr am hv hx hb)

theorem pop_m64_a32_effect_step [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (PopMemA32Pre p (3 + am.tail.length) 64 am)
      (codeRange p (0x67 :: 0x8F :: am.modrm 0 :: am.tail))
      (popM64A32Effect p (3 + am.tail.length) am) := by
  refine StepEffect.of_popMem32 (by decide) (by decide) am fun s h hcode ⟨hpre, hread⟩ => ?_
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := pop_m64_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow hread (by rw [hsc]; exact hpre.write)
  simp only [hsc] at hstep
  exact hstep

theorem pop_m64_a32_triple_of_bytes [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (PopMemA32Pre p (3 + am.tail.length) 64 am)
      (codeRange p (0x67 :: 0x8F :: am.modrm 0 :: am.tail))
      (Effect.post (popM64A32Effect p (3 + am.tail.length) am)) :=
  Triple.of_effect (fun _ hpre => popMemA32Effect_avoids (by simp; omega) am hpre)
    (pop_m64_a32_effect_step p am hv hx hb)

theorem pop_m64_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (PopMemA32Pre p (4 + am.tail.length) 64 am)
      (codeRange p (0x67 :: rex :: 0x8F :: am.modrm 0 :: am.tail))
      (popM64A32Effect p (4 + am.tail.length) am) := by
  refine StepEffect.of_popMem32 (by decide) (by decide) am fun s h hcode ⟨hpre, hread⟩ => ?_
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := pop_m64_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow hread (by rw [hsc]; exact hpre.write)
  simp only [hsc] at hstep
  exact hstep

theorem pop_m64_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (PopMemA32Pre p (4 + am.tail.length) 64 am)
      (codeRange p (0x67 :: rex :: 0x8F :: am.modrm 0 :: am.tail))
      (Effect.post (popM64A32Effect p (4 + am.tail.length) am)) :=
  Triple.of_effect (fun _ hpre => popMemA32Effect_avoids (by simp; omega) am hpre)
    (pop_m64_rex_a32_effect_step p rex hr am hv hx hb)

theorem pop_m64_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (PopMemPre p (encodePopM64 am).length 64 am)
      (codeRange p (encodePopM64 am))
      (Effect.post (popM64Effect p (encodePopM64 am).length am)) := by
  unfold encodePopM64
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := pop_m64_triple_of_bytes p am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 = 2 + am.tail.length by omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := pop_m64_rex_triple_of_bytes p _ hrex.rexPrefix am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]

theorem pop_m64_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (PopMemSegPre p (r.prefixByte :: encodePopM64 am).length 64 r base am)
      (codeRange p (r.prefixByte :: encodePopM64 am))
      (Effect.post (popM64SegEffect p (r.prefixByte :: encodePopM64 am).length base am)) := by
  unfold encodePopM64
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := pop_m64_seg_triple_of_bytes p r base am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := pop_m64_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem pop_m64_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (PopMemA32Pre p (0x67 :: encodePopM64 am).length 64 am)
      (codeRange p (0x67 :: encodePopM64 am))
      (Effect.post (popM64A32Effect p (0x67 :: encodePopM64 am).length am)) := by
  unfold encodePopM64
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := pop_m64_a32_triple_of_bytes p am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := pop_m64_rex_a32_triple_of_bytes p _ hrex.rexPrefix am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

def popM16Effect (p : BitVec 64) (len : Nat) (am : AddrMode) : RamState → Effect :=
  popMemEffect p len 16 am

def popM16SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode) :
    RamState → Effect :=
  popMemSegEffect p len 16 base am

def popM16A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) : RamState → Effect :=
  popMemA32Effect p len 16 am

theorem pop_m16_effect_step [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (PopMemPre p (3 + am.tail.length) 16 am)
      (codeRange p (0x66 :: 0x8F :: am.modrm 0 :: am.tail))
      (popM16Effect p (3 + am.tail.length) am) := by
  refine StepEffect.of_popMem (by decide) (by decide) am fun s h hcode ⟨hpre, hread⟩ => ?_
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := pop_m16_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    (by rfl) (by rfl)
    (by rfl) (by rfl)
    (by rfl)
    am hv (by exact (AddrContext.osz _ am hx hb).toSeg)
    hcode.bytesAt hlow hread (by exact hpre.write)
  exact hstep

theorem pop_m16_triple_of_bytes [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (PopMemPre p (3 + am.tail.length) 16 am)
      (codeRange p (0x66 :: 0x8F :: am.modrm 0 :: am.tail))
      (Effect.post (popM16Effect p (3 + am.tail.length) am)) :=
  Triple.of_effect (fun _ hpre => popMemEffect_avoids (by simp; omega) am hpre)
    (pop_m16_effect_step p am hv hx hb)

theorem pop_m16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (PopMemPre p (4 + am.tail.length) 16 am)
      (codeRange p (0x66 :: rex :: 0x8F :: am.modrm 0 :: am.tail))
      (popM16Effect p (4 + am.tail.length) am) := by
  have hr := hrex.rexPrefix
  refine StepEffect.of_popMem (by decide) (by decide) am fun s h hcode ⟨hpre, hread⟩ => ?_
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := pop_m16_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.rex_w_osz s.DS)
    am hv (by rw [scanContext_66_rex _ _ hr]; exact (AddrContext.oszRex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow hread (by rw [scanContext_66_rex _ _ hr]; exact hpre.write)
  simp only [scanContext_66_rex _ _ hr] at hstep
  exact hstep

theorem pop_m16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (PopMemPre p (4 + am.tail.length) 16 am)
      (codeRange p (0x66 :: rex :: 0x8F :: am.modrm 0 :: am.tail))
      (Effect.post (popM16Effect p (4 + am.tail.length) am)) :=
  Triple.of_effect (fun _ hpre => popMemEffect_avoids (by simp; omega) am hpre)
    (pop_m16_rex_effect_step p rex hrex am hv hx hb)

theorem pop_m16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (PopMemSegPre p (4 + am.tail.length) 16 r base am)
      (codeRange p (r.prefixByte :: 0x66 :: 0x8F :: am.modrm 0 :: am.tail))
      (popM16SegEffect p (4 + am.tail.length) base am) := by
  refine StepEffect.of_popMemSeg (by decide) (by decide) r base am
    fun s h hcode hpre => ?_
  obtain ⟨⟨⟨hp, hw, -⟩, hseg, hbase⟩, hread⟩ := hpre
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
  have hstep := pop_m16_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    am hv (by rw [hsc]; exact (AddrContext.osz _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow hread (by rw [hsc, segAddr_withSeg]; exact hw)
  simp only [hsc] at hstep
  exact hstep

theorem pop_m16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (PopMemSegPre p (4 + am.tail.length) 16 r base am)
      (codeRange p (r.prefixByte :: 0x66 :: 0x8F :: am.modrm 0 :: am.tail))
      (Effect.post (popM16SegEffect p (4 + am.tail.length) base am)) :=
  Triple.of_effect (fun _ hpre => popMemSegEffect_avoids (by simp; omega) am hpre)
    (pop_m16_seg_effect_step p r base am hv hx hb)

theorem pop_m16_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (PopMemSegPre p (5 + am.tail.length) 16 r base am)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x8F :: am.modrm 0 :: am.tail))
      (popM16SegEffect p (5 + am.tail.length) base am) := by
  have hr := hrex.rexPrefix
  refine StepEffect.of_popMemSeg (by decide) (by decide) r base am
    fun s h hcode hpre => ?_
  obtain ⟨⟨⟨hp, hw, -⟩, hseg, hbase⟩, hread⟩ := hpre
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
  have hstep := pop_m16_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; exact hrex.rex_w_osz s.DS)
    am hv (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow hread (by rw [hsc, segAddr_withSeg]; exact hw)
  simp only [hsc] at hstep
  exact hstep

theorem pop_m16_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (PopMemSegPre p (5 + am.tail.length) 16 r base am)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x8F :: am.modrm 0 :: am.tail))
      (Effect.post (popM16SegEffect p (5 + am.tail.length) base am)) :=
  Triple.of_effect (fun _ hpre => popMemSegEffect_avoids (by simp; omega) am hpre)
    (pop_m16_rex_seg_effect_step p r base rex hrex am hv hx hb)

theorem pop_m16_a32_effect_step [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (PopMemA32Pre p (4 + am.tail.length) 16 am)
      (codeRange p (0x67 :: 0x66 :: 0x8F :: am.modrm 0 :: am.tail))
      (popM16A32Effect p (4 + am.tail.length) am) := by
  refine StepEffect.of_popMem32 (by decide) (by decide) am fun s h hcode ⟨hpre, hread⟩ => ?_
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66]) := by
    rw [scanContext_asz_cons]
  have hstep := pop_m16_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    am hv (by rw [hsc]; exact (AddrContext.osz _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow hread (by rw [hsc]; exact hpre.write)
  simp only [hsc] at hstep
  exact hstep

theorem pop_m16_a32_triple_of_bytes [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (PopMemA32Pre p (4 + am.tail.length) 16 am)
      (codeRange p (0x67 :: 0x66 :: 0x8F :: am.modrm 0 :: am.tail))
      (Effect.post (popM16A32Effect p (4 + am.tail.length) am)) :=
  Triple.of_effect (fun _ hpre => popMemA32Effect_avoids (by simp; omega) am hpre)
    (pop_m16_a32_effect_step p am hv hx hb)

theorem pop_m16_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (PopMemA32Pre p (5 + am.tail.length) 16 am)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x8F :: am.modrm 0 :: am.tail))
      (popM16A32Effect p (5 + am.tail.length) am) := by
  have hr := hrex.rexPrefix
  refine StepEffect.of_popMem32 (by decide) (by decide) am fun s h hcode ⟨hpre, hread⟩ => ?_
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66, rex] =
      withAsz (oszRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_66_rex _ _ hr]
  have hstep := pop_m16_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; exact hrex.rex_w_osz s.DS)
    am hv (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow hread (by rw [hsc]; exact hpre.write)
  simp only [hsc] at hstep
  exact hstep

theorem pop_m16_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (PopMemA32Pre p (5 + am.tail.length) 16 am)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x8F :: am.modrm 0 :: am.tail))
      (Effect.post (popM16A32Effect p (5 + am.tail.length) am)) :=
  Triple.of_effect (fun _ hpre => popMemA32Effect_avoids (by simp; omega) am hpre)
    (pop_m16_rex_a32_effect_step p rex hrex am hv hx hb)

theorem pop_m16_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (PopMemPre p (encodePopM16 am).length 16 am)
      (codeRange p (encodePopM16 am))
      (Effect.post (popM16Effect p (encodePopM16 am).length am)) := by
  unfold encodePopM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := pop_m16_triple_of_bytes p am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := pop_m16_rex_triple_of_bytes p _ hrex am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem pop_m16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (PopMemSegPre p (r.prefixByte :: encodePopM16 am).length 16 r base am)
      (codeRange p (r.prefixByte :: encodePopM16 am))
      (Effect.post (popM16SegEffect p (r.prefixByte :: encodePopM16 am).length base am)) := by
  unfold encodePopM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := pop_m16_seg_triple_of_bytes p r base am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := pop_m16_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

theorem pop_m16_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (PopMemA32Pre p (0x67 :: encodePopM16 am).length 16 am)
      (codeRange p (0x67 :: encodePopM16 am))
      (Effect.post (popM16A32Effect p (0x67 :: encodePopM16 am).length am)) := by
  unfold encodePopM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := pop_m16_a32_triple_of_bytes p am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := pop_m16_rex_a32_triple_of_bytes p _ hrex am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

attribute [x86_compose] popM64Effect popM64SegEffect popM64A32Effect popM16Effect popM16SegEffect popM16A32Effect

@[x86_local] theorem popM64Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (popM64Effect p len am) :=
  popMemEffect_local (by decide)

@[x86_local] theorem popM64SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} : Effect.Local (popM64SegEffect p len base am) :=
  popMemSegEffect_local (by decide)

@[x86_local] theorem popM64A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (popM64A32Effect p len am) :=
  popMemA32Effect_local (by decide)

@[x86_local] theorem popM16Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (popM16Effect p len am) :=
  popMemEffect_local (by decide)

@[x86_local] theorem popM16SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} : Effect.Local (popM16SegEffect p len base am) :=
  popMemSegEffect_local (by decide)

@[x86_local] theorem popM16A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (popM16A32Effect p len am) :=
  popMemA32Effect_local (by decide)

end X86Proofs
