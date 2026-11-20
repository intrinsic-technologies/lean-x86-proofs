import X86Proofs.Instructions.Push.Generated.M.Step
import X86Proofs.Instructions.Push.Generated.M.Encode
import X86Proofs.Instructions.Push.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def pushM64Effect (p : BitVec 64) (len : Nat) (am : AddrMode) : RamState → Effect :=
  pushEffect (fun _ => p + BitVec.ofNat 64 len)
    fun s => (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s

@[simp] theorem pushM64Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (s : RamState) :
    (pushM64Effect p len am s).components = [.reg 4, .mem (pushAddr s) 8, .rip] :=
  pushEffect_components _ _ s

abbrev PushMemPre (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Prop :=
  PushPre p len s ∧ MemReadable s (am.addr s (p + BitVec.ofNat 64 len)) 8

def pushM64SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode) :
    RamState → Effect :=
  pushEffect (fun _ => p + BitVec.ofNat 64 len)
    fun s => (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 64).read s

@[simp] theorem pushM64SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (am : AddrMode) (s : RamState) :
    (pushM64SegEffect p len base am s).components = [.reg 4, .mem (pushAddr s) 8, .rip] :=
  pushEffect_components _ _ s

abbrev PushMemSegPre (p : BitVec 64) (len : Nat) (r : SegReg) (base : BitVec 64) (am : AddrMode)
    (s : RamState) : Prop :=
  PushPre p len s ∧ r.Ready base s ∧
    MemReadable s (base + am.addr s (p + BitVec.ofNat 64 len)) 8

def pushM64A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) : RamState → Effect :=
  pushEffect (fun _ => p + BitVec.ofNat 64 len)
    fun s => (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 64).read s

@[simp] theorem pushM64A32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (s : RamState) :
    (pushM64A32Effect p len am s).components = [.reg 4, .mem (pushAddr s) 8, .rip] :=
  pushEffect_components _ _ s

abbrev PushMemA32Pre (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Prop :=
  PushPre p len s ∧ MemReadable s (am.addr32 s (p + BitVec.ofNat 64 len)) 8

theorem push_m64_effect_step [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (PushMemPre p (2 + am.tail.length) am) (codeRange p (0xFF :: am.modrm 6 :: am.tail))
      (pushM64Effect p (2 + am.tail.length) am) := by
  refine StepEffect.of_pushLoad _ (fun _ h => h.1) fun s h hcode ⟨hpre, hread⟩ => ?_
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := push_m64_step s h [] (by simp) (by simp)
    (by rfl) (by rfl)
    (by rfl) (by rfl)
    am hv (by exact (AddrContext.legacy _ am hx hb).toSeg) hcode.bytesAt hlow
    (by exact hread) hpre.write
  exact hstep

theorem push_m64_triple_of_bytes [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (PushMemPre p (2 + am.tail.length) am) (codeRange p (0xFF :: am.modrm 6 :: am.tail))
      (Effect.post (pushM64Effect p (2 + am.tail.length) am)) :=
  Triple.of_effect
    (fun _ hpre => pushEffect_avoids (by simp; omega) _ _ hpre.1)
    (push_m64_effect_step p am hv hx hb)

theorem push_m64_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (PushMemPre p (3 + am.tail.length) am) (codeRange p (rex :: 0xFF :: am.modrm 6 :: am.tail))
      (pushM64Effect p (3 + am.tail.length) am) := by
  refine StepEffect.of_pushLoad _ (fun _ h => h.1) fun s h hcode ⟨hpre, hread⟩ => ?_
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := push_m64_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    am hv (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg) hcode.bytesAt hlow
    (by rw [scanContext_rex _ _ hr]; exact hread) hpre.write
  simp only [scanContext_rex _ _ hr] at hstep
  exact hstep

theorem push_m64_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (PushMemPre p (3 + am.tail.length) am) (codeRange p (rex :: 0xFF :: am.modrm 6 :: am.tail))
      (Effect.post (pushM64Effect p (3 + am.tail.length) am)) :=
  Triple.of_effect
    (fun _ hpre => pushEffect_avoids (by simp; omega) _ _ hpre.1)
    (push_m64_rex_effect_step p rex hr am hv hx hb)

theorem push_m64_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (PushMemSegPre p (3 + am.tail.length) r base am) (codeRange p (r.prefixByte :: 0xFF :: am.modrm 6 :: am.tail))
      (pushM64SegEffect p (3 + am.tail.length) base am) := by
  refine StepEffect.of_pushLoad _ (fun _ h => h.1)
    fun s h hcode ⟨hpre, ⟨hseg, hbase⟩, hread⟩ => ?_
  have hp := hpre.rip
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
  have hstep := push_m64_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg) hcode.bytesAt hlow
    (by rw [hsc, segAddr_withSeg]; exact hread) hpre.write
  simp only [hsc, segAddr_withSeg] at hstep
  exact hstep

theorem push_m64_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (PushMemSegPre p (3 + am.tail.length) r base am) (codeRange p (r.prefixByte :: 0xFF :: am.modrm 6 :: am.tail))
      (Effect.post (pushM64SegEffect p (3 + am.tail.length) base am)) :=
  Triple.of_effect
    (fun _ hpre => pushEffect_avoids (by simp; omega) _ _ hpre.1)
    (push_m64_seg_effect_step p r base am hv hx hb)

theorem push_m64_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (PushMemSegPre p (4 + am.tail.length) r base am) (codeRange p (r.prefixByte :: rex :: 0xFF :: am.modrm 6 :: am.tail))
      (pushM64SegEffect p (4 + am.tail.length) base am) := by
  refine StepEffect.of_pushLoad _ (fun _ h => h.1)
    fun s h hcode ⟨hpre, ⟨hseg, hbase⟩, hread⟩ => ?_
  have hp := hpre.rip
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
  have hstep := push_m64_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg) hcode.bytesAt hlow
    (by rw [hsc, segAddr_withSeg]; exact hread) hpre.write
  simp only [hsc, segAddr_withSeg] at hstep
  exact hstep

theorem push_m64_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (PushMemSegPre p (4 + am.tail.length) r base am) (codeRange p (r.prefixByte :: rex :: 0xFF :: am.modrm 6 :: am.tail))
      (Effect.post (pushM64SegEffect p (4 + am.tail.length) base am)) :=
  Triple.of_effect
    (fun _ hpre => pushEffect_avoids (by simp; omega) _ _ hpre.1)
    (push_m64_rex_seg_effect_step p r base rex hr am hv hx hb)

theorem push_m64_a32_effect_step [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (PushMemA32Pre p (3 + am.tail.length) am) (codeRange p (0x67 :: 0xFF :: am.modrm 6 :: am.tail))
      (pushM64A32Effect p (3 + am.tail.length) am) := by
  refine StepEffect.of_pushLoad _ (fun _ h => h.1) fun s h hcode ⟨hpre, hread⟩ => ?_
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
  have hstep := push_m64_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    am hv (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz) hcode.bytesAt hlow
    (by rw [hsc]; exact hread) hpre.write
  simp only [hsc] at hstep
  exact hstep

theorem push_m64_a32_triple_of_bytes [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (PushMemA32Pre p (3 + am.tail.length) am) (codeRange p (0x67 :: 0xFF :: am.modrm 6 :: am.tail))
      (Effect.post (pushM64A32Effect p (3 + am.tail.length) am)) :=
  Triple.of_effect
    (fun _ hpre => pushEffect_avoids (by simp; omega) _ _ hpre.1)
    (push_m64_a32_effect_step p am hv hx hb)

theorem push_m64_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (PushMemA32Pre p (4 + am.tail.length) am) (codeRange p (0x67 :: rex :: 0xFF :: am.modrm 6 :: am.tail))
      (pushM64A32Effect p (4 + am.tail.length) am) := by
  refine StepEffect.of_pushLoad _ (fun _ h => h.1) fun s h hcode ⟨hpre, hread⟩ => ?_
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
  have hstep := push_m64_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    am hv (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz) hcode.bytesAt hlow
    (by rw [hsc]; exact hread) hpre.write
  simp only [hsc] at hstep
  exact hstep

theorem push_m64_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (PushMemA32Pre p (4 + am.tail.length) am) (codeRange p (0x67 :: rex :: 0xFF :: am.modrm 6 :: am.tail))
      (Effect.post (pushM64A32Effect p (4 + am.tail.length) am)) :=
  Triple.of_effect
    (fun _ hpre => pushEffect_avoids (by simp; omega) _ _ hpre.1)
    (push_m64_rex_a32_effect_step p rex hr am hv hx hb)

theorem push_m64_triple [Bindings] (p : BitVec 64) (am : AddrMode)
    (hv : am.Valid) :
    Triple (PushMemPre p (encodePushM64 am).length am)
      (codeRange p (encodePushM64 am))
      (Effect.post (pushM64Effect p (encodePushM64 am).length am)) := by
  unfold encodePushM64
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := push_m64_triple_of_bytes p am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 = 2 + am.tail.length by omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := push_m64_rex_triple_of_bytes p _ hrex.rexPrefix am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]

theorem push_m64_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) (am : AddrMode)
    (hv : am.Valid) :
    Triple (PushMemSegPre p (r.prefixByte :: encodePushM64 am).length r base am)
      (codeRange p (r.prefixByte :: encodePushM64 am))
      (Effect.post (pushM64SegEffect p (r.prefixByte :: encodePushM64 am).length base am)) := by
  unfold encodePushM64
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := push_m64_seg_triple_of_bytes p r base am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := push_m64_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem push_m64_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (PushMemA32Pre p (0x67 :: encodePushM64 am).length am)
      (codeRange p (0x67 :: encodePushM64 am))
      (Effect.post (pushM64A32Effect p (0x67 :: encodePushM64 am).length am)) := by
  unfold encodePushM64
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := push_m64_a32_triple_of_bytes p am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := push_m64_rex_a32_triple_of_bytes p _ hrex.rexPrefix am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

attribute [x86_compose] pushM64Effect pushM64SegEffect pushM64A32Effect

@[x86_local] theorem pushM64Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (pushM64Effect p len am) := by
  effect_local [pushM64Effect, pushEffect, pushAddr, stackPtr]

@[x86_local] theorem pushM64SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} : Effect.Local (pushM64SegEffect p len base am) := by
  effect_local [pushM64SegEffect, pushEffect, pushAddr, stackPtr]

@[x86_local] theorem pushM64A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (pushM64A32Effect p len am) := by
  effect_local [pushM64A32Effect, pushEffect, pushAddr, stackPtr]

def pushM16Effect (p : BitVec 64) (len : Nat) (am : AddrMode) : RamState → Effect :=
  push16Effect (fun _ => p + BitVec.ofNat 64 len)
    fun s => (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 16).read s

@[simp] theorem pushM16Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (s : RamState) :
    (pushM16Effect p len am s).components = [.reg 4, .mem (pushAddr16 s) 2, .rip] :=
  push16Effect_components _ _ s

abbrev PushMem16Pre (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Prop :=
  Push16Pre p len s ∧ MemReadable s (am.addr s (p + BitVec.ofNat 64 len)) 2

def pushM16SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode) :
    RamState → Effect :=
  push16Effect (fun _ => p + BitVec.ofNat 64 len)
    fun s => (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 16).read s

@[simp] theorem pushM16SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (am : AddrMode) (s : RamState) :
    (pushM16SegEffect p len base am s).components = [.reg 4, .mem (pushAddr16 s) 2, .rip] :=
  push16Effect_components _ _ s

abbrev PushMem16SegPre (p : BitVec 64) (len : Nat) (r : SegReg) (base : BitVec 64) (am : AddrMode)
    (s : RamState) : Prop :=
  Push16Pre p len s ∧ r.Ready base s ∧
    MemReadable s (base + am.addr s (p + BitVec.ofNat 64 len)) 2

def pushM16A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) : RamState → Effect :=
  push16Effect (fun _ => p + BitVec.ofNat 64 len)
    fun s => (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 len)) : Operand 16).read s

@[simp] theorem pushM16A32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (s : RamState) :
    (pushM16A32Effect p len am s).components = [.reg 4, .mem (pushAddr16 s) 2, .rip] :=
  push16Effect_components _ _ s

abbrev PushMem16A32Pre (p : BitVec 64) (len : Nat) (am : AddrMode) (s : RamState) : Prop :=
  Push16Pre p len s ∧ MemReadable s (am.addr32 s (p + BitVec.ofNat 64 len)) 2

theorem push_m16_effect_step [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (PushMem16Pre p (3 + am.tail.length) am) (codeRange p (0x66 :: 0xFF :: am.modrm 6 :: am.tail))
      (pushM16Effect p (3 + am.tail.length) am) := by
  refine StepEffect.of_pushLoad16 _ (fun _ h => h.1) fun s h hcode ⟨hpre, hread⟩ => ?_
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := push_m16_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    (by rfl) (by rfl)
    (by rfl) (by rfl)
    (by rfl)
    am hv (by exact (AddrContext.osz _ am hx hb).toSeg) hcode.bytesAt hlow
    (by exact hread) hpre.write
  exact hstep

theorem push_m16_triple_of_bytes [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (PushMem16Pre p (3 + am.tail.length) am) (codeRange p (0x66 :: 0xFF :: am.modrm 6 :: am.tail))
      (Effect.post (pushM16Effect p (3 + am.tail.length) am)) :=
  Triple.of_effect
    (fun _ hpre => push16Effect_avoids (by simp; omega) _ _ hpre.1)
    (push_m16_effect_step p am hv hx hb)

theorem push_m16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (PushMem16Pre p (4 + am.tail.length) am) (codeRange p (0x66 :: rex :: 0xFF :: am.modrm 6 :: am.tail))
      (pushM16Effect p (4 + am.tail.length) am) := by
  have hr := hrex.rexPrefix
  refine StepEffect.of_pushLoad16 _ (fun _ h => h.1) fun s h hcode ⟨hpre, hread⟩ => ?_
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := push_m16_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.rex_w_osz s.DS)
    am hv (by rw [scanContext_66_rex _ _ hr]; exact (AddrContext.oszRex _ _ am hx hb).toSeg) hcode.bytesAt hlow
    (by rw [scanContext_66_rex _ _ hr]; exact hread) hpre.write
  simp only [scanContext_66_rex _ _ hr] at hstep
  exact hstep

theorem push_m16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (PushMem16Pre p (4 + am.tail.length) am) (codeRange p (0x66 :: rex :: 0xFF :: am.modrm 6 :: am.tail))
      (Effect.post (pushM16Effect p (4 + am.tail.length) am)) :=
  Triple.of_effect
    (fun _ hpre => push16Effect_avoids (by simp; omega) _ _ hpre.1)
    (push_m16_rex_effect_step p rex hrex am hv hx hb)

theorem push_m16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (PushMem16SegPre p (4 + am.tail.length) r base am) (codeRange p (r.prefixByte :: 0x66 :: 0xFF :: am.modrm 6 :: am.tail))
      (pushM16SegEffect p (4 + am.tail.length) base am) := by
  refine StepEffect.of_pushLoad16 _ (fun _ h => h.1)
    fun s h hcode ⟨hpre, ⟨hseg, hbase⟩, hread⟩ => ?_
  have hp := hpre.rip
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
  have hstep := push_m16_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    am hv (by rw [hsc]; exact (AddrContext.osz _ am hx hb).withSeg hseg) hcode.bytesAt hlow
    (by rw [hsc, segAddr_withSeg]; exact hread) hpre.write
  simp only [hsc, segAddr_withSeg] at hstep
  exact hstep

theorem push_m16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (PushMem16SegPre p (4 + am.tail.length) r base am) (codeRange p (r.prefixByte :: 0x66 :: 0xFF :: am.modrm 6 :: am.tail))
      (Effect.post (pushM16SegEffect p (4 + am.tail.length) base am)) :=
  Triple.of_effect
    (fun _ hpre => push16Effect_avoids (by simp; omega) _ _ hpre.1)
    (push_m16_seg_effect_step p r base am hv hx hb)

theorem push_m16_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (PushMem16SegPre p (5 + am.tail.length) r base am) (codeRange p (r.prefixByte :: 0x66 :: rex :: 0xFF :: am.modrm 6 :: am.tail))
      (pushM16SegEffect p (5 + am.tail.length) base am) := by
  have hr := hrex.rexPrefix
  refine StepEffect.of_pushLoad16 _ (fun _ h => h.1)
    fun s h hcode ⟨hpre, ⟨hseg, hbase⟩, hread⟩ => ?_
  have hp := hpre.rip
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
  have hstep := push_m16_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; exact hrex.rex_w_osz s.DS)
    am hv (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).withSeg hseg) hcode.bytesAt hlow
    (by rw [hsc, segAddr_withSeg]; exact hread) hpre.write
  simp only [hsc, segAddr_withSeg] at hstep
  exact hstep

theorem push_m16_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (PushMem16SegPre p (5 + am.tail.length) r base am) (codeRange p (r.prefixByte :: 0x66 :: rex :: 0xFF :: am.modrm 6 :: am.tail))
      (Effect.post (pushM16SegEffect p (5 + am.tail.length) base am)) :=
  Triple.of_effect
    (fun _ hpre => push16Effect_avoids (by simp; omega) _ _ hpre.1)
    (push_m16_rex_seg_effect_step p r base rex hrex am hv hx hb)

theorem push_m16_a32_effect_step [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (PushMem16A32Pre p (4 + am.tail.length) am) (codeRange p (0x67 :: 0x66 :: 0xFF :: am.modrm 6 :: am.tail))
      (pushM16A32Effect p (4 + am.tail.length) am) := by
  refine StepEffect.of_pushLoad16 _ (fun _ h => h.1) fun s h hcode ⟨hpre, hread⟩ => ?_
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
  have hstep := push_m16_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    am hv (by rw [hsc]; exact (AddrContext.osz _ am hx hb).toSeg.withAsz) hcode.bytesAt hlow
    (by rw [hsc]; exact hread) hpre.write
  simp only [hsc] at hstep
  exact hstep

theorem push_m16_a32_triple_of_bytes [Bindings] (p : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (PushMem16A32Pre p (4 + am.tail.length) am) (codeRange p (0x67 :: 0x66 :: 0xFF :: am.modrm 6 :: am.tail))
      (Effect.post (pushM16A32Effect p (4 + am.tail.length) am)) :=
  Triple.of_effect
    (fun _ hpre => push16Effect_avoids (by simp; omega) _ _ hpre.1)
    (push_m16_a32_effect_step p am hv hx hb)

theorem push_m16_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (PushMem16A32Pre p (5 + am.tail.length) am) (codeRange p (0x67 :: 0x66 :: rex :: 0xFF :: am.modrm 6 :: am.tail))
      (pushM16A32Effect p (5 + am.tail.length) am) := by
  have hr := hrex.rexPrefix
  refine StepEffect.of_pushLoad16 _ (fun _ h => h.1) fun s h hcode ⟨hpre, hread⟩ => ?_
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
  have hstep := push_m16_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; exact hrex.rex_w_osz s.DS)
    am hv (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg.withAsz) hcode.bytesAt hlow
    (by rw [hsc]; exact hread) hpre.write
  simp only [hsc] at hstep
  exact hstep

theorem push_m16_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (PushMem16A32Pre p (5 + am.tail.length) am) (codeRange p (0x67 :: 0x66 :: rex :: 0xFF :: am.modrm 6 :: am.tail))
      (Effect.post (pushM16A32Effect p (5 + am.tail.length) am)) :=
  Triple.of_effect
    (fun _ hpre => push16Effect_avoids (by simp; omega) _ _ hpre.1)
    (push_m16_rex_a32_effect_step p rex hrex am hv hx hb)

theorem push_m16_triple [Bindings] (p : BitVec 64) (am : AddrMode)
    (hv : am.Valid) :
    Triple (PushMem16Pre p (encodePushM16 am).length am)
      (codeRange p (encodePushM16 am))
      (Effect.post (pushM16Effect p (encodePushM16 am).length am)) := by
  unfold encodePushM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := push_m16_triple_of_bytes p am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 = 3 + am.tail.length by omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := push_m16_rex_triple_of_bytes p _ hrex am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]

theorem push_m16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) (am : AddrMode)
    (hv : am.Valid) :
    Triple (PushMem16SegPre p (r.prefixByte :: encodePushM16 am).length r base am)
      (codeRange p (r.prefixByte :: encodePushM16 am))
      (Effect.post (pushM16SegEffect p (r.prefixByte :: encodePushM16 am).length base am)) := by
  unfold encodePushM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := push_m16_seg_triple_of_bytes p r base am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := push_m16_rex_seg_triple_of_bytes p r base _ hrex am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

theorem push_m16_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid) :
    Triple (PushMem16A32Pre p (0x67 :: encodePushM16 am).length am)
      (codeRange p (0x67 :: encodePushM16 am))
      (Effect.post (pushM16A32Effect p (0x67 :: encodePushM16 am).length am)) := by
  unfold encodePushM16
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := push_m16_a32_triple_of_bytes p am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 = 4 + am.tail.length by omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := push_m16_rex_a32_triple_of_bytes p _ hrex am hv hx hb
    simp only [List.length_cons]
    rwa [show am.tail.length + 1 + 1 + 1 + 1 + 1 = 5 + am.tail.length by omega]

attribute [x86_compose] pushM16Effect pushM16SegEffect pushM16A32Effect

@[x86_local] theorem pushM16Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (pushM16Effect p len am) := by
  effect_local [pushM16Effect, push16Effect, pushAddr16, stackPtr]

@[x86_local] theorem pushM16SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} : Effect.Local (pushM16SegEffect p len base am) := by
  effect_local [pushM16SegEffect, push16Effect, pushAddr16, stackPtr]

@[x86_local] theorem pushM16A32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode} :
    Effect.Local (pushM16A32Effect p len am) := by
  effect_local [pushM16A32Effect, push16Effect, pushAddr16, stackPtr]

end X86Proofs
