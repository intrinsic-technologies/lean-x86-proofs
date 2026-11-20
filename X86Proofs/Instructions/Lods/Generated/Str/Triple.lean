import X86Proofs.Instructions.Lods.Generated.Str.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def lodsqEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.reg 0 : Operand 64), (Operand.mem (rsi.read s) : Operand 64).read s⟩,
    ⟨rsi, rsi.read s + 8⟩]

@[simp] theorem lodsqEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (lodsqEffect p len s).components = [.reg 0, .reg 6, .rip] := by
  simp [lodsqEffect, Effect.components]

theorem lodsq_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (LodsPre p 8) (codeRange p [rex, 0xAD]) (lodsqEffect p 2) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hdf, hrd⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := lodsq_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    hdf hcode.bytesAt hlow hrd
  exact ⟨_, hstep, ReadyToStep.afterStep_lods h _ _ _,
    ⟨afterStep_lods_rip h _ _ _, ⟨(Operand.read_afterStep_lods_rax _ _ _ _).trans (mergeGPR_64 _ _),
      Operand.read_afterStep_lods_rsi _ _ _ _⟩,
      trivial,
      AgreesExcept.afterStep_lods _ _ _ _⟩⟩

theorem lodsq_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    Triple (LodsPre p 8) (codeRange p [rex, 0xAD]) (Effect.post (lodsqEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lodsqEffect_components]; simp [Component.Covers]) _)
    (lodsq_effect_step p rex hrex)

theorem lodsq_triple [Bindings] (p : BitVec 64) :
    Triple (LodsPre p 8) (codeRange p [0x48, 0xAD]) (Effect.post (lodsqEffect p 2)) :=
  lodsq_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide)

def lodsqSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.reg 0 : Operand 64), (Operand.mem (base + rsi.read s) : Operand 64).read s⟩,
    ⟨rsi, rsi.read s + 8⟩]

@[simp] theorem lodsqSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (s : RamState) : (lodsqSegEffect p len base s).components = [.reg 0, .reg 6, .rip] := by
  simp [lodsqSegEffect, Effect.components]

theorem lodsq_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (LodsSegPre p 8 r base) (codeRange p [r.prefixByte, rex, 0xAD])
      (lodsqSegEffect p 3 base) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hdf, hrd, ⟨hseg, hbase⟩⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex] (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := lodsq_seg_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hrex.rex_w s.DS)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    hdf hcode.bytesAt hlow (by rw [hsc]; exact hrd)
  rw [hsc] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_lods_seg h _ _ _,
    ⟨afterStep_lods_seg_rip h _ _ _, ⟨(Operand.read_afterStep_lods_seg_rax _ _ _ _).trans (mergeGPR_64 _ _),
      Operand.read_afterStep_lods_seg_rsi _ _ _ _⟩,
      trivial,
      AgreesExcept.afterStep_lods_seg _ _ _ _⟩⟩

theorem lodsq_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    Triple (LodsSegPre p 8 r base) (codeRange p [r.prefixByte, rex, 0xAD])
      (Effect.post (lodsqSegEffect p 3 base)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lodsqSegEffect_components]; simp [Component.Covers]) _)
    (lodsq_seg_effect_step p r base rex hrex)

theorem lodsq_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (LodsSegPre p 8 r base) (codeRange p [r.prefixByte, 0x48, 0xAD])
      (Effect.post (lodsqSegEffect p 3 base)) :=
  lodsq_seg_triple_of_bytes p r base 0x48 (by unfold RexWPrefix; decide)

def lodsdEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.reg 0 : Operand 64), ((Operand.mem (rsi.read s) : Operand 32).read s).setWidth 64⟩,
    ⟨rsi, rsi.read s + 4⟩]

@[simp] theorem lodsdEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (lodsdEffect p len s).components = [.reg 0, .reg 6, .rip] := by
  simp [lodsdEffect, Effect.components]

theorem lodsd_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (LodsPre p 4) (codeRange p [0xAD]) (lodsdEffect p 1) := by
  rintro s h hcode ⟨hp, hdf, hrd⟩
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := lodsd_step s h [] (by simp) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hrd
  exact ⟨_, hstep, ReadyToStep.afterStep_lods h _ _ _,
    ⟨afterStep_lods_rip h _ _ _, ⟨(Operand.read_afterStep_lods_rax _ _ _ _).trans (mergeGPR_32 _ _),
      Operand.read_afterStep_lods_rsi _ _ _ _⟩,
      trivial,
      AgreesExcept.afterStep_lods _ _ _ _⟩⟩

theorem lodsd_triple [Bindings] (p : BitVec 64) :
    Triple (LodsPre p 4) (codeRange p [0xAD]) (Effect.post (lodsdEffect p 1)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lodsdEffect_components]; simp [Component.Covers]) _)
    (lodsd_effect_step p)

def lodsdSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.reg 0 : Operand 64), ((Operand.mem (base + rsi.read s) : Operand 32).read s).setWidth 64⟩,
    ⟨rsi, rsi.read s + 4⟩]

@[simp] theorem lodsdSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (s : RamState) : (lodsdSegEffect p len base s).components = [.reg 0, .reg 6, .rip] := by
  simp [lodsdSegEffect, Effect.components]

theorem lodsd_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    StepEffect (LodsSegPre p 4 r base) (codeRange p [r.prefixByte, 0xAD])
      (lodsdSegEffect p 2 base) := by
  rintro s h hcode ⟨hp, hdf, hrd, ⟨hseg, hbase⟩⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [] noSegPrefix_nil]
  have hstep := lodsd_seg_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    hdf hcode.bytesAt hlow (by rw [hsc]; exact hrd)
  rw [hsc] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_lods_seg h _ _ _,
    ⟨afterStep_lods_seg_rip h _ _ _, ⟨(Operand.read_afterStep_lods_seg_rax _ _ _ _).trans (mergeGPR_32 _ _),
      Operand.read_afterStep_lods_seg_rsi _ _ _ _⟩,
      trivial,
      AgreesExcept.afterStep_lods_seg _ _ _ _⟩⟩

theorem lodsd_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (LodsSegPre p 4 r base) (codeRange p [r.prefixByte, 0xAD])
      (Effect.post (lodsdSegEffect p 2 base)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lodsdSegEffect_components]; simp [Component.Covers]) _)
    (lodsd_seg_effect_step p r base)

def lodswEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.reg 0 : Operand 64), mergeGPR 16 ((Operand.mem (rsi.read s) : Operand 16).read s)
      ((Operand.reg 0 : Operand 64).read s)⟩,
    ⟨rsi, rsi.read s + 2⟩]

@[simp] theorem lodswEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (lodswEffect p len s).components = [.reg 0, .reg 6, .rip] := by
  simp [lodswEffect, Effect.components]

theorem lodsw_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (LodsPre p 2) (codeRange p [0x66, 0xAD]) (lodswEffect p 2) := by
  rintro s h hcode ⟨hp, hdf, hrd⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := lodsw_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hrd
  exact ⟨_, hstep, ReadyToStep.afterStep_lods h _ _ _,
    ⟨afterStep_lods_rip h _ _ _, ⟨Operand.read_afterStep_lods_rax _ _ _ _,
      Operand.read_afterStep_lods_rsi _ _ _ _⟩,
      trivial,
      AgreesExcept.afterStep_lods _ _ _ _⟩⟩

theorem lodsw_triple [Bindings] (p : BitVec 64) :
    Triple (LodsPre p 2) (codeRange p [0x66, 0xAD]) (Effect.post (lodswEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lodswEffect_components]; simp [Component.Covers]) _)
    (lodsw_effect_step p)

def lodswSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.reg 0 : Operand 64), mergeGPR 16 ((Operand.mem (base + rsi.read s) : Operand 16).read s)
      ((Operand.reg 0 : Operand 64).read s)⟩,
    ⟨rsi, rsi.read s + 2⟩]

@[simp] theorem lodswSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (s : RamState) : (lodswSegEffect p len base s).components = [.reg 0, .reg 6, .rip] := by
  simp [lodswSegEffect, Effect.components]

theorem lodsw_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    StepEffect (LodsSegPre p 2 r base) (codeRange p [r.prefixByte, 0x66, 0xAD])
      (lodswSegEffect p 3 base) := by
  rintro s h hcode ⟨hp, hdf, hrd, ⟨hseg, hbase⟩⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66] (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil)]
  have hstep := lodsw_seg_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    hdf hcode.bytesAt hlow (by rw [hsc]; exact hrd)
  rw [hsc] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_lods_seg h _ _ _,
    ⟨afterStep_lods_seg_rip h _ _ _, ⟨Operand.read_afterStep_lods_seg_rax _ _ _ _,
      Operand.read_afterStep_lods_seg_rsi _ _ _ _⟩,
      trivial,
      AgreesExcept.afterStep_lods_seg _ _ _ _⟩⟩

theorem lodsw_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (LodsSegPre p 2 r base) (codeRange p [r.prefixByte, 0x66, 0xAD])
      (Effect.post (lodswSegEffect p 3 base)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lodswSegEffect_components]; simp [Component.Covers]) _)
    (lodsw_seg_effect_step p r base)

def lodsbEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.reg 0 : Operand 64), mergeGPR 8 ((Operand.mem (rsi.read s) : Operand 8).read s)
      ((Operand.reg 0 : Operand 64).read s)⟩,
    ⟨rsi, rsi.read s + 1⟩]

@[simp] theorem lodsbEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (lodsbEffect p len s).components = [.reg 0, .reg 6, .rip] := by
  simp [lodsbEffect, Effect.components]

theorem lodsb_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (LodsPre p 1) (codeRange p [0xAC]) (lodsbEffect p 1) := by
  rintro s h hcode ⟨hp, hdf, hrd⟩
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := lodsb_step s h [] (by simp) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hrd
  exact ⟨_, hstep, ReadyToStep.afterStep_lods h _ _ _,
    ⟨afterStep_lods_rip h _ _ _, ⟨Operand.read_afterStep_lods_rax _ _ _ _,
      Operand.read_afterStep_lods_rsi _ _ _ _⟩,
      trivial,
      AgreesExcept.afterStep_lods _ _ _ _⟩⟩

theorem lodsb_triple [Bindings] (p : BitVec 64) :
    Triple (LodsPre p 1) (codeRange p [0xAC]) (Effect.post (lodsbEffect p 1)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lodsbEffect_components]; simp [Component.Covers]) _)
    (lodsb_effect_step p)

def lodsbSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.reg 0 : Operand 64), mergeGPR 8 ((Operand.mem (base + rsi.read s) : Operand 8).read s)
      ((Operand.reg 0 : Operand 64).read s)⟩,
    ⟨rsi, rsi.read s + 1⟩]

@[simp] theorem lodsbSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (s : RamState) : (lodsbSegEffect p len base s).components = [.reg 0, .reg 6, .rip] := by
  simp [lodsbSegEffect, Effect.components]

theorem lodsb_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    StepEffect (LodsSegPre p 1 r base) (codeRange p [r.prefixByte, 0xAC])
      (lodsbSegEffect p 2 base) := by
  rintro s h hcode ⟨hp, hdf, hrd, ⟨hseg, hbase⟩⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [] noSegPrefix_nil]
  have hstep := lodsb_seg_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    hdf hcode.bytesAt hlow (by rw [hsc]; exact hrd)
  rw [hsc] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_lods_seg h _ _ _,
    ⟨afterStep_lods_seg_rip h _ _ _, ⟨Operand.read_afterStep_lods_seg_rax _ _ _ _,
      Operand.read_afterStep_lods_seg_rsi _ _ _ _⟩,
      trivial,
      AgreesExcept.afterStep_lods_seg _ _ _ _⟩⟩

theorem lodsb_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (LodsSegPre p 1 r base) (codeRange p [r.prefixByte, 0xAC])
      (Effect.post (lodsbSegEffect p 2 base)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lodsbSegEffect_components]; simp [Component.Covers]) _)
    (lodsb_seg_effect_step p r base)

theorem lodsq_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (fun s => LodsPre p 8 s ∧ (rsi.read s).toNat + 8 < 2^32) (codeRange p [0x67, rex, 0xAD])
      (lodsqEffect p 3) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, hdf, hrd⟩, hsl⟩
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := lodsq_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    hdf hcode.bytesAt hlow hrd hsl
  exact ⟨_, hstep, ReadyToStep.afterStep_lods h _ _ _,
    ⟨afterStep_lods_rip h _ _ _, ⟨(Operand.read_afterStep_lods_rax _ _ _ _).trans (mergeGPR_64 _ _),
      Operand.read_afterStep_lods_rsi _ _ _ _⟩,
      trivial,
      AgreesExcept.afterStep_lods _ _ _ _⟩⟩

theorem lodsq_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    Triple (fun s => LodsPre p 8 s ∧ (rsi.read s).toNat + 8 < 2^32) (codeRange p [0x67, rex, 0xAD])
      (Effect.post (lodsqEffect p 3)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lodsqEffect_components]; simp [Component.Covers]) _)
    (lodsq_a32_effect_step p rex hrex)

theorem lodsq_a32_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => LodsPre p 8 s ∧ (rsi.read s).toNat + 8 < 2^32) (codeRange p [0x67, 0x48, 0xAD])
      (Effect.post (lodsqEffect p 3)) :=
  lodsq_a32_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide)

theorem lodsd_a32_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => LodsPre p 4 s ∧ (rsi.read s).toNat + 4 < 2^32) (codeRange p [0x67, 0xAD])
      (lodsdEffect p 2) := by
  rintro s h hcode ⟨⟨hp, hdf, hrd⟩, hsl⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := lodsd_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    hdf hcode.bytesAt hlow hrd hsl
  exact ⟨_, hstep, ReadyToStep.afterStep_lods h _ _ _,
    ⟨afterStep_lods_rip h _ _ _, ⟨(Operand.read_afterStep_lods_rax _ _ _ _).trans (mergeGPR_32 _ _),
      Operand.read_afterStep_lods_rsi _ _ _ _⟩,
      trivial,
      AgreesExcept.afterStep_lods _ _ _ _⟩⟩

theorem lodsd_a32_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => LodsPre p 4 s ∧ (rsi.read s).toNat + 4 < 2^32) (codeRange p [0x67, 0xAD])
      (Effect.post (lodsdEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lodsdEffect_components]; simp [Component.Covers]) _)
    (lodsd_a32_effect_step p)

theorem lodsw_a32_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => LodsPre p 2 s ∧ (rsi.read s).toNat + 2 < 2^32) (codeRange p [0x67, 0x66, 0xAD])
      (lodswEffect p 3) := by
  rintro s h hcode ⟨⟨hp, hdf, hrd⟩, hsl⟩
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := lodsw_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    hdf hcode.bytesAt hlow hrd hsl
  exact ⟨_, hstep, ReadyToStep.afterStep_lods h _ _ _,
    ⟨afterStep_lods_rip h _ _ _, ⟨Operand.read_afterStep_lods_rax _ _ _ _,
      Operand.read_afterStep_lods_rsi _ _ _ _⟩,
      trivial,
      AgreesExcept.afterStep_lods _ _ _ _⟩⟩

theorem lodsw_a32_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => LodsPre p 2 s ∧ (rsi.read s).toNat + 2 < 2^32) (codeRange p [0x67, 0x66, 0xAD])
      (Effect.post (lodswEffect p 3)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lodswEffect_components]; simp [Component.Covers]) _)
    (lodsw_a32_effect_step p)

theorem lodsb_a32_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => LodsPre p 1 s ∧ (rsi.read s).toNat + 1 < 2^32) (codeRange p [0x67, 0xAC])
      (lodsbEffect p 2) := by
  rintro s h hcode ⟨⟨hp, hdf, hrd⟩, hsl⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := lodsb_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    hdf hcode.bytesAt hlow hrd hsl
  exact ⟨_, hstep, ReadyToStep.afterStep_lods h _ _ _,
    ⟨afterStep_lods_rip h _ _ _, ⟨Operand.read_afterStep_lods_rax _ _ _ _,
      Operand.read_afterStep_lods_rsi _ _ _ _⟩,
      trivial,
      AgreesExcept.afterStep_lods _ _ _ _⟩⟩

theorem lodsb_a32_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => LodsPre p 1 s ∧ (rsi.read s).toNat + 1 < 2^32) (codeRange p [0x67, 0xAC])
      (Effect.post (lodsbEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lodsbEffect_components]; simp [Component.Covers]) _)
    (lodsb_a32_effect_step p)

attribute [x86_compose] lodsqEffect lodsqSegEffect lodsdEffect lodsdSegEffect lodswEffect lodswSegEffect lodsbEffect lodsbSegEffect

@[x86_local] theorem lodsqEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (lodsqEffect p len) := by
  effect_local [lodsqEffect]

@[x86_local] theorem lodsqSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} :
    Effect.Local (lodsqSegEffect p len base) := by
  effect_local [lodsqSegEffect]

@[x86_local] theorem lodsdEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (lodsdEffect p len) := by
  effect_local [lodsdEffect]

@[x86_local] theorem lodsdSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} :
    Effect.Local (lodsdSegEffect p len base) := by
  effect_local [lodsdSegEffect]

@[x86_local] theorem lodswEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (lodswEffect p len) := by
  effect_local [lodswEffect]

@[x86_local] theorem lodswSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} :
    Effect.Local (lodswSegEffect p len base) := by
  effect_local [lodswSegEffect]

@[x86_local] theorem lodsbEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (lodsbEffect p len) := by
  effect_local [lodsbEffect]

@[x86_local] theorem lodsbSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} :
    Effect.Local (lodsbSegEffect p len base) := by
  effect_local [lodsbSegEffect]

end X86Proofs
