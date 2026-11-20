import X86Proofs.Instructions.Movs.Generated.Str.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movsqEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s + 8⟩, ⟨rdi, rdi.read s + 8⟩,
    ⟨(Operand.mem (rdi.read s) : Operand 64), (Operand.mem (rsi.read s) : Operand 64).read s⟩]

@[simp] theorem movsqEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (movsqEffect p len s).components = [.reg 6, .reg 7, .mem (rdi.read s) 8, .rip] := by
  simp [movsqEffect, Effect.components]

theorem movsq_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (MovsPre p 2 8) (codeRange p [rex, 0xA5]) (movsqEffect p 2) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hdf, hrd, hwr, _⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := movsq_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    hdf hcode.bytesAt hlow hrd hwr
  exact ⟨_, hstep, ReadyToStep.afterStep_movs h _ _ _ hwr,
    ⟨afterStep_movs_rip h _ _ _, ⟨Operand.read_afterStep_movs_rsi _ _ _ _,
      Operand.read_afterStep_movs_rdi _ _ _ _,
      Operand.read_afterStep_movs_mem _ _ (n := 64) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_movs _ _ _ _⟩⟩

theorem movsq_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    Triple (MovsPre p 2 8) (codeRange p [rex, 0xA5]) (Effect.post (movsqEffect p 2)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.code rfl)
    (movsq_effect_step p rex hrex)

theorem movsq_triple [Bindings] (p : BitVec 64) :
    Triple (MovsPre p 2 8) (codeRange p [0x48, 0xA5]) (Effect.post (movsqEffect p 2)) :=
  movsq_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide)

def movsqSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s + 8⟩, ⟨rdi, rdi.read s + 8⟩,
    ⟨(Operand.mem (rdi.read s) : Operand 64),
      (Operand.mem (base + rsi.read s) : Operand 64).read s⟩]

@[simp] theorem movsqSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (s : RamState) : (movsqSegEffect p len base s).components = [.reg 6, .reg 7, .mem (rdi.read s) 8, .rip] := by
  simp [movsqSegEffect, Effect.components]

theorem movsq_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (MovsSegPre p 3 8 r base) (codeRange p [r.prefixByte, rex, 0xA5])
      (movsqSegEffect p 3 base) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hdf, hrd, hwr, _, ⟨hseg, hbase⟩⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex] (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := movsq_seg_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hrex.rex_w s.DS)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    hdf hcode.bytesAt hlow (by rw [hsc]; exact hrd) hwr
  rw [hsc] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_movs_seg h _ _ _ hwr,
    ⟨afterStep_movs_seg_rip h _ _ _, ⟨Operand.read_afterStep_movs_seg_rsi _ _ _ _,
      Operand.read_afterStep_movs_seg_rdi _ _ _ _,
      Operand.read_afterStep_movs_seg_mem _ _ (n := 64) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_movs_seg _ _ _ _⟩⟩

theorem movsq_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    Triple (MovsSegPre p 3 8 r base) (codeRange p [r.prefixByte, rex, 0xA5])
      (Effect.post (movsqSegEffect p 3 base)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.code rfl)
    (movsq_seg_effect_step p r base rex hrex)

theorem movsq_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (MovsSegPre p 3 8 r base) (codeRange p [r.prefixByte, 0x48, 0xA5])
      (Effect.post (movsqSegEffect p 3 base)) :=
  movsq_seg_triple_of_bytes p r base 0x48 (by unfold RexWPrefix; decide)

def movsdEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s + 4⟩, ⟨rdi, rdi.read s + 4⟩,
    ⟨(Operand.mem (rdi.read s) : Operand 32), (Operand.mem (rsi.read s) : Operand 32).read s⟩]

@[simp] theorem movsdEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (movsdEffect p len s).components = [.reg 6, .reg 7, .mem (rdi.read s) 4, .rip] := by
  simp [movsdEffect, Effect.components]

theorem movsd_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (MovsPre p 1 4) (codeRange p [0xA5]) (movsdEffect p 1) := by
  rintro s h hcode ⟨hp, hdf, hrd, hwr, _⟩
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := movsd_step s h [] (by simp) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hrd hwr
  exact ⟨_, hstep, ReadyToStep.afterStep_movs h _ _ _ hwr,
    ⟨afterStep_movs_rip h _ _ _, ⟨Operand.read_afterStep_movs_rsi _ _ _ _,
      Operand.read_afterStep_movs_rdi _ _ _ _,
      Operand.read_afterStep_movs_mem _ _ (n := 32) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_movs _ _ _ _⟩⟩

theorem movsd_triple [Bindings] (p : BitVec 64) :
    Triple (MovsPre p 1 4) (codeRange p [0xA5]) (Effect.post (movsdEffect p 1)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.code rfl)
    (movsd_effect_step p)

def movsdSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s + 4⟩, ⟨rdi, rdi.read s + 4⟩,
    ⟨(Operand.mem (rdi.read s) : Operand 32),
      (Operand.mem (base + rsi.read s) : Operand 32).read s⟩]

@[simp] theorem movsdSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (s : RamState) : (movsdSegEffect p len base s).components = [.reg 6, .reg 7, .mem (rdi.read s) 4, .rip] := by
  simp [movsdSegEffect, Effect.components]

theorem movsd_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    StepEffect (MovsSegPre p 2 4 r base) (codeRange p [r.prefixByte, 0xA5])
      (movsdSegEffect p 2 base) := by
  rintro s h hcode ⟨hp, hdf, hrd, hwr, _, ⟨hseg, hbase⟩⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [] noSegPrefix_nil]
  have hstep := movsd_seg_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    hdf hcode.bytesAt hlow (by rw [hsc]; exact hrd) hwr
  rw [hsc] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_movs_seg h _ _ _ hwr,
    ⟨afterStep_movs_seg_rip h _ _ _, ⟨Operand.read_afterStep_movs_seg_rsi _ _ _ _,
      Operand.read_afterStep_movs_seg_rdi _ _ _ _,
      Operand.read_afterStep_movs_seg_mem _ _ (n := 32) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_movs_seg _ _ _ _⟩⟩

theorem movsd_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (MovsSegPre p 2 4 r base) (codeRange p [r.prefixByte, 0xA5])
      (Effect.post (movsdSegEffect p 2 base)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.code rfl)
    (movsd_seg_effect_step p r base)

def movswEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s + 2⟩, ⟨rdi, rdi.read s + 2⟩,
    ⟨(Operand.mem (rdi.read s) : Operand 16), (Operand.mem (rsi.read s) : Operand 16).read s⟩]

@[simp] theorem movswEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (movswEffect p len s).components = [.reg 6, .reg 7, .mem (rdi.read s) 2, .rip] := by
  simp [movswEffect, Effect.components]

theorem movsw_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (MovsPre p 2 2) (codeRange p [0x66, 0xA5]) (movswEffect p 2) := by
  rintro s h hcode ⟨hp, hdf, hrd, hwr, _⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := movsw_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hrd hwr
  exact ⟨_, hstep, ReadyToStep.afterStep_movs h _ _ _ hwr,
    ⟨afterStep_movs_rip h _ _ _, ⟨Operand.read_afterStep_movs_rsi _ _ _ _,
      Operand.read_afterStep_movs_rdi _ _ _ _,
      Operand.read_afterStep_movs_mem _ _ (n := 16) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_movs _ _ _ _⟩⟩

theorem movsw_triple [Bindings] (p : BitVec 64) :
    Triple (MovsPre p 2 2) (codeRange p [0x66, 0xA5]) (Effect.post (movswEffect p 2)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.code rfl)
    (movsw_effect_step p)

def movswSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s + 2⟩, ⟨rdi, rdi.read s + 2⟩,
    ⟨(Operand.mem (rdi.read s) : Operand 16),
      (Operand.mem (base + rsi.read s) : Operand 16).read s⟩]

@[simp] theorem movswSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (s : RamState) : (movswSegEffect p len base s).components = [.reg 6, .reg 7, .mem (rdi.read s) 2, .rip] := by
  simp [movswSegEffect, Effect.components]

theorem movsw_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    StepEffect (MovsSegPre p 3 2 r base) (codeRange p [r.prefixByte, 0x66, 0xA5])
      (movswSegEffect p 3 base) := by
  rintro s h hcode ⟨hp, hdf, hrd, hwr, _, ⟨hseg, hbase⟩⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66] (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil)]
  have hstep := movsw_seg_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    hdf hcode.bytesAt hlow (by rw [hsc]; exact hrd) hwr
  rw [hsc] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_movs_seg h _ _ _ hwr,
    ⟨afterStep_movs_seg_rip h _ _ _, ⟨Operand.read_afterStep_movs_seg_rsi _ _ _ _,
      Operand.read_afterStep_movs_seg_rdi _ _ _ _,
      Operand.read_afterStep_movs_seg_mem _ _ (n := 16) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_movs_seg _ _ _ _⟩⟩

theorem movsw_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (MovsSegPre p 3 2 r base) (codeRange p [r.prefixByte, 0x66, 0xA5])
      (Effect.post (movswSegEffect p 3 base)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.code rfl)
    (movsw_seg_effect_step p r base)

def movsbSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s + 1⟩, ⟨rdi, rdi.read s + 1⟩,
    ⟨(Operand.mem (rdi.read s) : Operand 8),
      (Operand.mem (base + rsi.read s) : Operand 8).read s⟩]

@[simp] theorem movsbSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (s : RamState) : (movsbSegEffect p len base s).components = [.reg 6, .reg 7, .mem (rdi.read s) 1, .rip] := by
  simp [movsbSegEffect, Effect.components]

theorem movsb_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    StepEffect (MovsSegPre p 2 1 r base) (codeRange p [r.prefixByte, 0xA4])
      (movsbSegEffect p 2 base) := by
  rintro s h hcode ⟨hp, hdf, hrd, hwr, _, ⟨hseg, hbase⟩⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [] noSegPrefix_nil]
  have hstep := movsb_seg_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    hdf hcode.bytesAt hlow (by rw [hsc]; exact hrd) hwr
  rw [hsc] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_movs_seg h _ _ _ hwr,
    ⟨afterStep_movs_seg_rip h _ _ _, ⟨Operand.read_afterStep_movs_seg_rsi _ _ _ _,
      Operand.read_afterStep_movs_seg_rdi _ _ _ _,
      Operand.read_afterStep_movs_seg_mem _ _ (n := 8) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_movs_seg _ _ _ _⟩⟩

theorem movsb_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (MovsSegPre p 2 1 r base) (codeRange p [r.prefixByte, 0xA4])
      (Effect.post (movsbSegEffect p 2 base)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.code rfl)
    (movsb_seg_effect_step p r base)

theorem movsq_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (fun s => MovsPre p 3 8 s ∧ (rsi.read s).toNat + 8 < 2^32 ∧ (rdi.read s).toNat + 8 < 2^32) (codeRange p [0x67, rex, 0xA5])
      (movsqEffect p 3) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, hdf, hrd, hwr, _⟩, hsl, hdl⟩
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := movsq_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    hdf hcode.bytesAt hlow hrd hwr hsl hdl
  exact ⟨_, hstep, ReadyToStep.afterStep_movs h _ _ _ hwr,
    ⟨afterStep_movs_rip h _ _ _, ⟨Operand.read_afterStep_movs_rsi _ _ _ _,
      Operand.read_afterStep_movs_rdi _ _ _ _,
      Operand.read_afterStep_movs_mem _ _ (n := 64) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_movs _ _ _ _⟩⟩

theorem movsq_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    Triple (fun s => MovsPre p 3 8 s ∧ (rsi.read s).toNat + 8 < 2^32 ∧ (rdi.read s).toNat + 8 < 2^32) (codeRange p [0x67, rex, 0xA5])
      (Effect.post (movsqEffect p 3)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.1.code rfl)
    (movsq_a32_effect_step p rex hrex)

theorem movsq_a32_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => MovsPre p 3 8 s ∧ (rsi.read s).toNat + 8 < 2^32 ∧ (rdi.read s).toNat + 8 < 2^32) (codeRange p [0x67, 0x48, 0xA5])
      (Effect.post (movsqEffect p 3)) :=
  movsq_a32_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide)

theorem movsd_a32_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => MovsPre p 2 4 s ∧ (rsi.read s).toNat + 4 < 2^32 ∧ (rdi.read s).toNat + 4 < 2^32) (codeRange p [0x67, 0xA5])
      (movsdEffect p 2) := by
  rintro s h hcode ⟨⟨hp, hdf, hrd, hwr, _⟩, hsl, hdl⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := movsd_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    hdf hcode.bytesAt hlow hrd hwr hsl hdl
  exact ⟨_, hstep, ReadyToStep.afterStep_movs h _ _ _ hwr,
    ⟨afterStep_movs_rip h _ _ _, ⟨Operand.read_afterStep_movs_rsi _ _ _ _,
      Operand.read_afterStep_movs_rdi _ _ _ _,
      Operand.read_afterStep_movs_mem _ _ (n := 32) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_movs _ _ _ _⟩⟩

theorem movsd_a32_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => MovsPre p 2 4 s ∧ (rsi.read s).toNat + 4 < 2^32 ∧ (rdi.read s).toNat + 4 < 2^32) (codeRange p [0x67, 0xA5])
      (Effect.post (movsdEffect p 2)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.1.code rfl)
    (movsd_a32_effect_step p)

theorem movsw_a32_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => MovsPre p 3 2 s ∧ (rsi.read s).toNat + 2 < 2^32 ∧ (rdi.read s).toNat + 2 < 2^32) (codeRange p [0x67, 0x66, 0xA5])
      (movswEffect p 3) := by
  rintro s h hcode ⟨⟨hp, hdf, hrd, hwr, _⟩, hsl, hdl⟩
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := movsw_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    hdf hcode.bytesAt hlow hrd hwr hsl hdl
  exact ⟨_, hstep, ReadyToStep.afterStep_movs h _ _ _ hwr,
    ⟨afterStep_movs_rip h _ _ _, ⟨Operand.read_afterStep_movs_rsi _ _ _ _,
      Operand.read_afterStep_movs_rdi _ _ _ _,
      Operand.read_afterStep_movs_mem _ _ (n := 16) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_movs _ _ _ _⟩⟩

theorem movsw_a32_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => MovsPre p 3 2 s ∧ (rsi.read s).toNat + 2 < 2^32 ∧ (rdi.read s).toNat + 2 < 2^32) (codeRange p [0x67, 0x66, 0xA5])
      (Effect.post (movswEffect p 3)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.1.code rfl)
    (movsw_a32_effect_step p)

def movsbA32Effect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s + 1⟩, ⟨rdi, rdi.read s + 1⟩,
    ⟨(Operand.mem (rdi.read s) : Operand 8), (Operand.mem (rsi.read s) : Operand 8).read s⟩]

@[simp] theorem movsbA32Effect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (movsbA32Effect p len s).components = [.reg 6, .reg 7, .mem (rdi.read s) 1, .rip] := by
  simp [movsbA32Effect, Effect.components]

theorem movsb_a32_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => MovsPre p 2 1 s ∧ (rsi.read s).toNat + 1 < 2^32 ∧ (rdi.read s).toNat + 1 < 2^32) (codeRange p [0x67, 0xA4])
      (movsbA32Effect p 2) := by
  rintro s h hcode ⟨⟨hp, hdf, hrd, hwr, _⟩, hsl, hdl⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := movsb_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    hdf hcode.bytesAt hlow hrd hwr hsl hdl
  exact ⟨_, hstep, ReadyToStep.afterStep_movs h _ _ _ hwr,
    ⟨afterStep_movs_rip h _ _ _, ⟨Operand.read_afterStep_movs_rsi _ _ _ _,
      Operand.read_afterStep_movs_rdi _ _ _ _,
      Operand.read_afterStep_movs_mem _ _ (n := 8) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_movs _ _ _ _⟩⟩

theorem movsb_a32_triple [Bindings] (p : BitVec 64) :
    Triple (fun s => MovsPre p 2 1 s ∧ (rsi.read s).toNat + 1 < 2^32 ∧ (rdi.read s).toNat + 1 < 2^32) (codeRange p [0x67, 0xA4])
      (Effect.post (movsbA32Effect p 2)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.1.code rfl)
    (movsb_a32_effect_step p)

attribute [x86_compose] movsqEffect movsqSegEffect movsdEffect movsdSegEffect movswEffect movswSegEffect movsbSegEffect movsbA32Effect

@[x86_local] theorem movsqEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (movsqEffect p len) := by
  effect_local [movsqEffect]

@[x86_local] theorem movsqSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} :
    Effect.Local (movsqSegEffect p len base) := by
  effect_local [movsqSegEffect]

@[x86_local] theorem movsdEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (movsdEffect p len) := by
  effect_local [movsdEffect]

@[x86_local] theorem movsdSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} :
    Effect.Local (movsdSegEffect p len base) := by
  effect_local [movsdSegEffect]

@[x86_local] theorem movswEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (movswEffect p len) := by
  effect_local [movswEffect]

@[x86_local] theorem movswSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} :
    Effect.Local (movswSegEffect p len base) := by
  effect_local [movswSegEffect]

@[x86_local] theorem movsbSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} :
    Effect.Local (movsbSegEffect p len base) := by
  effect_local [movsbSegEffect]

@[x86_local] theorem movsbA32Effect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (movsbA32Effect p len) := by
  effect_local [movsbA32Effect]

end X86Proofs
