import X86Proofs.Instructions.Movs.Generated.StrDown.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movsqDownEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s - 8⟩, ⟨rdi, rdi.read s - 8⟩,
    ⟨(Operand.mem (rdi.read s) : Operand 64), (Operand.mem (rsi.read s) : Operand 64).read s⟩]

@[simp] theorem movsqDownEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (movsqDownEffect p len s).components = [.reg 6, .reg 7, .mem (rdi.read s) 8, .rip] := by
  simp [movsqDownEffect, Effect.components]

theorem movsq_down_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (MovsDownPre p 2 8) (codeRange p [rex, 0xA5]) (movsqDownEffect p 2) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hdf, hrd, hwr, _⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := movsq_down_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    hdf hcode.bytesAt hlow hrd hwr
  exact ⟨_, hstep, ReadyToStep.afterStep_movs_down h _ _ _ hwr,
    ⟨afterStep_movs_down_rip h _ _ _, ⟨Operand.read_afterStep_movs_down_rsi _ _ _ _,
      Operand.read_afterStep_movs_down_rdi _ _ _ _,
      Operand.read_afterStep_movs_down_mem _ _ (n := 64) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_movs_down _ _ _ _⟩⟩

theorem movsq_down_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    Triple (MovsDownPre p 2 8) (codeRange p [rex, 0xA5]) (Effect.post (movsqDownEffect p 2)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.code rfl)
    (movsq_down_effect_step p rex hrex)

theorem movsq_down_triple [Bindings] (p : BitVec 64) :
    Triple (MovsDownPre p 2 8) (codeRange p [0x48, 0xA5]) (Effect.post (movsqDownEffect p 2)) :=
  movsq_down_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide)

def movsqDownSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s - 8⟩, ⟨rdi, rdi.read s - 8⟩,
    ⟨(Operand.mem (rdi.read s) : Operand 64),
      (Operand.mem (base + rsi.read s) : Operand 64).read s⟩]

@[simp] theorem movsqDownSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (s : RamState) : (movsqDownSegEffect p len base s).components = [.reg 6, .reg 7, .mem (rdi.read s) 8, .rip] := by
  simp [movsqDownSegEffect, Effect.components]

theorem movsq_down_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (MovsDownSegPre p 3 8 r base) (codeRange p [r.prefixByte, rex, 0xA5])
      (movsqDownSegEffect p 3 base) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hdf, hrd, hwr, _, ⟨hseg, hbase⟩⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex] (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := movsq_down_seg_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hrex.rex_w s.DS)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    hdf hcode.bytesAt hlow (by rw [hsc]; exact hrd) hwr
  rw [hsc] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_movs_down_seg h _ _ _ hwr,
    ⟨afterStep_movs_down_seg_rip h _ _ _, ⟨Operand.read_afterStep_movs_down_seg_rsi _ _ _ _,
      Operand.read_afterStep_movs_down_seg_rdi _ _ _ _,
      Operand.read_afterStep_movs_down_seg_mem _ _ (n := 64) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_movs_down_seg _ _ _ _⟩⟩

theorem movsq_down_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    Triple (MovsDownSegPre p 3 8 r base) (codeRange p [r.prefixByte, rex, 0xA5])
      (Effect.post (movsqDownSegEffect p 3 base)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.code rfl)
    (movsq_down_seg_effect_step p r base rex hrex)

theorem movsq_down_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (MovsDownSegPre p 3 8 r base) (codeRange p [r.prefixByte, 0x48, 0xA5])
      (Effect.post (movsqDownSegEffect p 3 base)) :=
  movsq_down_seg_triple_of_bytes p r base 0x48 (by unfold RexWPrefix; decide)

def movsdDownEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s - 4⟩, ⟨rdi, rdi.read s - 4⟩,
    ⟨(Operand.mem (rdi.read s) : Operand 32), (Operand.mem (rsi.read s) : Operand 32).read s⟩]

@[simp] theorem movsdDownEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (movsdDownEffect p len s).components = [.reg 6, .reg 7, .mem (rdi.read s) 4, .rip] := by
  simp [movsdDownEffect, Effect.components]

theorem movsd_down_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (MovsDownPre p 1 4) (codeRange p [0xA5]) (movsdDownEffect p 1) := by
  rintro s h hcode ⟨hp, hdf, hrd, hwr, _⟩
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := movsd_down_step s h [] (by simp) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hrd hwr
  exact ⟨_, hstep, ReadyToStep.afterStep_movs_down h _ _ _ hwr,
    ⟨afterStep_movs_down_rip h _ _ _, ⟨Operand.read_afterStep_movs_down_rsi _ _ _ _,
      Operand.read_afterStep_movs_down_rdi _ _ _ _,
      Operand.read_afterStep_movs_down_mem _ _ (n := 32) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_movs_down _ _ _ _⟩⟩

theorem movsd_down_triple [Bindings] (p : BitVec 64) :
    Triple (MovsDownPre p 1 4) (codeRange p [0xA5]) (Effect.post (movsdDownEffect p 1)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.code rfl)
    (movsd_down_effect_step p)

def movsdDownSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s - 4⟩, ⟨rdi, rdi.read s - 4⟩,
    ⟨(Operand.mem (rdi.read s) : Operand 32),
      (Operand.mem (base + rsi.read s) : Operand 32).read s⟩]

@[simp] theorem movsdDownSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (s : RamState) : (movsdDownSegEffect p len base s).components = [.reg 6, .reg 7, .mem (rdi.read s) 4, .rip] := by
  simp [movsdDownSegEffect, Effect.components]

theorem movsd_down_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    StepEffect (MovsDownSegPre p 2 4 r base) (codeRange p [r.prefixByte, 0xA5])
      (movsdDownSegEffect p 2 base) := by
  rintro s h hcode ⟨hp, hdf, hrd, hwr, _, ⟨hseg, hbase⟩⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [] noSegPrefix_nil]
  have hstep := movsd_down_seg_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
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
  exact ⟨_, hstep, ReadyToStep.afterStep_movs_down_seg h _ _ _ hwr,
    ⟨afterStep_movs_down_seg_rip h _ _ _, ⟨Operand.read_afterStep_movs_down_seg_rsi _ _ _ _,
      Operand.read_afterStep_movs_down_seg_rdi _ _ _ _,
      Operand.read_afterStep_movs_down_seg_mem _ _ (n := 32) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_movs_down_seg _ _ _ _⟩⟩

theorem movsd_down_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (MovsDownSegPre p 2 4 r base) (codeRange p [r.prefixByte, 0xA5])
      (Effect.post (movsdDownSegEffect p 2 base)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.code rfl)
    (movsd_down_seg_effect_step p r base)

def movswDownEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s - 2⟩, ⟨rdi, rdi.read s - 2⟩,
    ⟨(Operand.mem (rdi.read s) : Operand 16), (Operand.mem (rsi.read s) : Operand 16).read s⟩]

@[simp] theorem movswDownEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (movswDownEffect p len s).components = [.reg 6, .reg 7, .mem (rdi.read s) 2, .rip] := by
  simp [movswDownEffect, Effect.components]

theorem movsw_down_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (MovsDownPre p 2 2) (codeRange p [0x66, 0xA5]) (movswDownEffect p 2) := by
  rintro s h hcode ⟨hp, hdf, hrd, hwr, _⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := movsw_down_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hrd hwr
  exact ⟨_, hstep, ReadyToStep.afterStep_movs_down h _ _ _ hwr,
    ⟨afterStep_movs_down_rip h _ _ _, ⟨Operand.read_afterStep_movs_down_rsi _ _ _ _,
      Operand.read_afterStep_movs_down_rdi _ _ _ _,
      Operand.read_afterStep_movs_down_mem _ _ (n := 16) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_movs_down _ _ _ _⟩⟩

theorem movsw_down_triple [Bindings] (p : BitVec 64) :
    Triple (MovsDownPre p 2 2) (codeRange p [0x66, 0xA5]) (Effect.post (movswDownEffect p 2)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.code rfl)
    (movsw_down_effect_step p)

def movswDownSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s - 2⟩, ⟨rdi, rdi.read s - 2⟩,
    ⟨(Operand.mem (rdi.read s) : Operand 16),
      (Operand.mem (base + rsi.read s) : Operand 16).read s⟩]

@[simp] theorem movswDownSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (s : RamState) : (movswDownSegEffect p len base s).components = [.reg 6, .reg 7, .mem (rdi.read s) 2, .rip] := by
  simp [movswDownSegEffect, Effect.components]

theorem movsw_down_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    StepEffect (MovsDownSegPre p 3 2 r base) (codeRange p [r.prefixByte, 0x66, 0xA5])
      (movswDownSegEffect p 3 base) := by
  rintro s h hcode ⟨hp, hdf, hrd, hwr, _, ⟨hseg, hbase⟩⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66] (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil)]
  have hstep := movsw_down_seg_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
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
  exact ⟨_, hstep, ReadyToStep.afterStep_movs_down_seg h _ _ _ hwr,
    ⟨afterStep_movs_down_seg_rip h _ _ _, ⟨Operand.read_afterStep_movs_down_seg_rsi _ _ _ _,
      Operand.read_afterStep_movs_down_seg_rdi _ _ _ _,
      Operand.read_afterStep_movs_down_seg_mem _ _ (n := 16) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_movs_down_seg _ _ _ _⟩⟩

theorem movsw_down_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (MovsDownSegPre p 3 2 r base) (codeRange p [r.prefixByte, 0x66, 0xA5])
      (Effect.post (movswDownSegEffect p 3 base)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.code rfl)
    (movsw_down_seg_effect_step p r base)

def movsbDownEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s - 1⟩, ⟨rdi, rdi.read s - 1⟩,
    ⟨(Operand.mem (rdi.read s) : Operand 8), (Operand.mem (rsi.read s) : Operand 8).read s⟩]

@[simp] theorem movsbDownEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (movsbDownEffect p len s).components = [.reg 6, .reg 7, .mem (rdi.read s) 1, .rip] := by
  simp [movsbDownEffect, Effect.components]

theorem movsb_down_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (MovsDownPre p 1 1) (codeRange p [0xA4]) (movsbDownEffect p 1) := by
  rintro s h hcode ⟨hp, hdf, hrd, hwr, _⟩
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := movsb_down_step s h [] (by simp) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hrd hwr
  exact ⟨_, hstep, ReadyToStep.afterStep_movs_down h _ _ _ hwr,
    ⟨afterStep_movs_down_rip h _ _ _, ⟨Operand.read_afterStep_movs_down_rsi _ _ _ _,
      Operand.read_afterStep_movs_down_rdi _ _ _ _,
      Operand.read_afterStep_movs_down_mem _ _ (n := 8) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_movs_down _ _ _ _⟩⟩

theorem movsb_down_triple [Bindings] (p : BitVec 64) :
    Triple (MovsDownPre p 1 1) (codeRange p [0xA4]) (Effect.post (movsbDownEffect p 1)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.code rfl)
    (movsb_down_effect_step p)

def movsbDownSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s - 1⟩, ⟨rdi, rdi.read s - 1⟩,
    ⟨(Operand.mem (rdi.read s) : Operand 8),
      (Operand.mem (base + rsi.read s) : Operand 8).read s⟩]

@[simp] theorem movsbDownSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (s : RamState) : (movsbDownSegEffect p len base s).components = [.reg 6, .reg 7, .mem (rdi.read s) 1, .rip] := by
  simp [movsbDownSegEffect, Effect.components]

theorem movsb_down_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    StepEffect (MovsDownSegPre p 2 1 r base) (codeRange p [r.prefixByte, 0xA4])
      (movsbDownSegEffect p 2 base) := by
  rintro s h hcode ⟨hp, hdf, hrd, hwr, _, ⟨hseg, hbase⟩⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [] noSegPrefix_nil]
  have hstep := movsb_down_seg_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    hdf hcode.bytesAt hlow (by rw [hsc]; exact hrd) hwr
  rw [hsc] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_movs_down_seg h _ _ _ hwr,
    ⟨afterStep_movs_down_seg_rip h _ _ _, ⟨Operand.read_afterStep_movs_down_seg_rsi _ _ _ _,
      Operand.read_afterStep_movs_down_seg_rdi _ _ _ _,
      Operand.read_afterStep_movs_down_seg_mem _ _ (n := 8) (by decide) (by decide) _⟩,
      trivial,
      AgreesExcept.afterStep_movs_down_seg _ _ _ _⟩⟩

theorem movsb_down_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (MovsDownSegPre p 2 1 r base) (codeRange p [r.prefixByte, 0xA4])
      (Effect.post (movsbDownSegEffect p 2 base)) :=
  Triple.of_effect (fun _ hpre => Effect.avoids_of_mem (by simp [Component.isMem]) hpre.code rfl)
    (movsb_down_seg_effect_step p r base)

attribute [x86_compose] movsqDownEffect movsqDownSegEffect movsdDownEffect movsdDownSegEffect movswDownEffect movswDownSegEffect movsbDownEffect movsbDownSegEffect

@[x86_local] theorem movsqDownEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (movsqDownEffect p len) := by
  effect_local [movsqDownEffect]

@[x86_local] theorem movsqDownSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} :
    Effect.Local (movsqDownSegEffect p len base) := by
  effect_local [movsqDownSegEffect]

@[x86_local] theorem movsdDownEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (movsdDownEffect p len) := by
  effect_local [movsdDownEffect]

@[x86_local] theorem movsdDownSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} :
    Effect.Local (movsdDownSegEffect p len base) := by
  effect_local [movsdDownSegEffect]

@[x86_local] theorem movswDownEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (movswDownEffect p len) := by
  effect_local [movswDownEffect]

@[x86_local] theorem movswDownSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} :
    Effect.Local (movswDownSegEffect p len base) := by
  effect_local [movswDownSegEffect]

@[x86_local] theorem movsbDownEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (movsbDownEffect p len) := by
  effect_local [movsbDownEffect]

@[x86_local] theorem movsbDownSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} :
    Effect.Local (movsbDownSegEffect p len base) := by
  effect_local [movsbDownSegEffect]

end X86Proofs
