import X86Proofs.Instructions.Lods.Generated.StrDown.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def lodsqDownEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.reg 0 : Operand 64), (Operand.mem (rsi.read s) : Operand 64).read s⟩,
    ⟨rsi, rsi.read s - 8⟩]

@[simp] theorem lodsqDownEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (lodsqDownEffect p len s).components = [.reg 0, .reg 6, .rip] := by
  simp [lodsqDownEffect, Effect.components]

theorem lodsq_down_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (LodsDownPre p 8) (codeRange p [rex, 0xAD]) (lodsqDownEffect p 2) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hdf, hrd⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := lodsq_down_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    hdf hcode.bytesAt hlow hrd
  exact ⟨_, hstep, ReadyToStep.afterStep_lods_down h _ _ _,
    ⟨afterStep_lods_down_rip h _ _ _, ⟨(Operand.read_afterStep_lods_down_rax _ _ _ _).trans (mergeGPR_64 _ _),
      Operand.read_afterStep_lods_down_rsi _ _ _ _⟩,
      trivial,
      AgreesExcept.afterStep_lods_down _ _ _ _⟩⟩

theorem lodsq_down_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    Triple (LodsDownPre p 8) (codeRange p [rex, 0xAD]) (Effect.post (lodsqDownEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lodsqDownEffect_components]; simp [Component.Covers]) _)
    (lodsq_down_effect_step p rex hrex)

theorem lodsq_down_triple [Bindings] (p : BitVec 64) :
    Triple (LodsDownPre p 8) (codeRange p [0x48, 0xAD]) (Effect.post (lodsqDownEffect p 2)) :=
  lodsq_down_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide)

def lodsqDownSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.reg 0 : Operand 64), (Operand.mem (base + rsi.read s) : Operand 64).read s⟩,
    ⟨rsi, rsi.read s - 8⟩]

@[simp] theorem lodsqDownSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (s : RamState) : (lodsqDownSegEffect p len base s).components = [.reg 0, .reg 6, .rip] := by
  simp [lodsqDownSegEffect, Effect.components]

theorem lodsq_down_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (LodsDownSegPre p 8 r base) (codeRange p [r.prefixByte, rex, 0xAD])
      (lodsqDownSegEffect p 3 base) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hdf, hrd, ⟨hseg, hbase⟩⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex] (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := lodsq_down_seg_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hrex.rex_w s.DS)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    hdf hcode.bytesAt hlow (by rw [hsc]; exact hrd)
  rw [hsc] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_lods_down_seg h _ _ _,
    ⟨afterStep_lods_down_seg_rip h _ _ _, ⟨(Operand.read_afterStep_lods_down_seg_rax _ _ _ _).trans (mergeGPR_64 _ _),
      Operand.read_afterStep_lods_down_seg_rsi _ _ _ _⟩,
      trivial,
      AgreesExcept.afterStep_lods_down_seg _ _ _ _⟩⟩

theorem lodsq_down_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    Triple (LodsDownSegPre p 8 r base) (codeRange p [r.prefixByte, rex, 0xAD])
      (Effect.post (lodsqDownSegEffect p 3 base)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lodsqDownSegEffect_components]; simp [Component.Covers]) _)
    (lodsq_down_seg_effect_step p r base rex hrex)

theorem lodsq_down_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (LodsDownSegPre p 8 r base) (codeRange p [r.prefixByte, 0x48, 0xAD])
      (Effect.post (lodsqDownSegEffect p 3 base)) :=
  lodsq_down_seg_triple_of_bytes p r base 0x48 (by unfold RexWPrefix; decide)

def lodsdDownEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.reg 0 : Operand 64), ((Operand.mem (rsi.read s) : Operand 32).read s).setWidth 64⟩,
    ⟨rsi, rsi.read s - 4⟩]

@[simp] theorem lodsdDownEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (lodsdDownEffect p len s).components = [.reg 0, .reg 6, .rip] := by
  simp [lodsdDownEffect, Effect.components]

theorem lodsd_down_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (LodsDownPre p 4) (codeRange p [0xAD]) (lodsdDownEffect p 1) := by
  rintro s h hcode ⟨hp, hdf, hrd⟩
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := lodsd_down_step s h [] (by simp) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hrd
  exact ⟨_, hstep, ReadyToStep.afterStep_lods_down h _ _ _,
    ⟨afterStep_lods_down_rip h _ _ _, ⟨(Operand.read_afterStep_lods_down_rax _ _ _ _).trans (mergeGPR_32 _ _),
      Operand.read_afterStep_lods_down_rsi _ _ _ _⟩,
      trivial,
      AgreesExcept.afterStep_lods_down _ _ _ _⟩⟩

theorem lodsd_down_triple [Bindings] (p : BitVec 64) :
    Triple (LodsDownPre p 4) (codeRange p [0xAD]) (Effect.post (lodsdDownEffect p 1)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lodsdDownEffect_components]; simp [Component.Covers]) _)
    (lodsd_down_effect_step p)

def lodsdDownSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.reg 0 : Operand 64), ((Operand.mem (base + rsi.read s) : Operand 32).read s).setWidth 64⟩,
    ⟨rsi, rsi.read s - 4⟩]

@[simp] theorem lodsdDownSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (s : RamState) : (lodsdDownSegEffect p len base s).components = [.reg 0, .reg 6, .rip] := by
  simp [lodsdDownSegEffect, Effect.components]

theorem lodsd_down_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    StepEffect (LodsDownSegPre p 4 r base) (codeRange p [r.prefixByte, 0xAD])
      (lodsdDownSegEffect p 2 base) := by
  rintro s h hcode ⟨hp, hdf, hrd, ⟨hseg, hbase⟩⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [] noSegPrefix_nil]
  have hstep := lodsd_down_seg_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
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
  exact ⟨_, hstep, ReadyToStep.afterStep_lods_down_seg h _ _ _,
    ⟨afterStep_lods_down_seg_rip h _ _ _, ⟨(Operand.read_afterStep_lods_down_seg_rax _ _ _ _).trans (mergeGPR_32 _ _),
      Operand.read_afterStep_lods_down_seg_rsi _ _ _ _⟩,
      trivial,
      AgreesExcept.afterStep_lods_down_seg _ _ _ _⟩⟩

theorem lodsd_down_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (LodsDownSegPre p 4 r base) (codeRange p [r.prefixByte, 0xAD])
      (Effect.post (lodsdDownSegEffect p 2 base)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lodsdDownSegEffect_components]; simp [Component.Covers]) _)
    (lodsd_down_seg_effect_step p r base)

def lodswDownEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.reg 0 : Operand 64), mergeGPR 16 ((Operand.mem (rsi.read s) : Operand 16).read s)
      ((Operand.reg 0 : Operand 64).read s)⟩,
    ⟨rsi, rsi.read s - 2⟩]

@[simp] theorem lodswDownEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (lodswDownEffect p len s).components = [.reg 0, .reg 6, .rip] := by
  simp [lodswDownEffect, Effect.components]

theorem lodsw_down_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (LodsDownPre p 2) (codeRange p [0x66, 0xAD]) (lodswDownEffect p 2) := by
  rintro s h hcode ⟨hp, hdf, hrd⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := lodsw_down_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hrd
  exact ⟨_, hstep, ReadyToStep.afterStep_lods_down h _ _ _,
    ⟨afterStep_lods_down_rip h _ _ _, ⟨Operand.read_afterStep_lods_down_rax _ _ _ _,
      Operand.read_afterStep_lods_down_rsi _ _ _ _⟩,
      trivial,
      AgreesExcept.afterStep_lods_down _ _ _ _⟩⟩

theorem lodsw_down_triple [Bindings] (p : BitVec 64) :
    Triple (LodsDownPre p 2) (codeRange p [0x66, 0xAD]) (Effect.post (lodswDownEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lodswDownEffect_components]; simp [Component.Covers]) _)
    (lodsw_down_effect_step p)

def lodswDownSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.reg 0 : Operand 64), mergeGPR 16 ((Operand.mem (base + rsi.read s) : Operand 16).read s)
      ((Operand.reg 0 : Operand 64).read s)⟩,
    ⟨rsi, rsi.read s - 2⟩]

@[simp] theorem lodswDownSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (s : RamState) : (lodswDownSegEffect p len base s).components = [.reg 0, .reg 6, .rip] := by
  simp [lodswDownSegEffect, Effect.components]

theorem lodsw_down_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    StepEffect (LodsDownSegPre p 2 r base) (codeRange p [r.prefixByte, 0x66, 0xAD])
      (lodswDownSegEffect p 3 base) := by
  rintro s h hcode ⟨hp, hdf, hrd, ⟨hseg, hbase⟩⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66] (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil)]
  have hstep := lodsw_down_seg_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
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
  exact ⟨_, hstep, ReadyToStep.afterStep_lods_down_seg h _ _ _,
    ⟨afterStep_lods_down_seg_rip h _ _ _, ⟨Operand.read_afterStep_lods_down_seg_rax _ _ _ _,
      Operand.read_afterStep_lods_down_seg_rsi _ _ _ _⟩,
      trivial,
      AgreesExcept.afterStep_lods_down_seg _ _ _ _⟩⟩

theorem lodsw_down_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (LodsDownSegPre p 2 r base) (codeRange p [r.prefixByte, 0x66, 0xAD])
      (Effect.post (lodswDownSegEffect p 3 base)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lodswDownSegEffect_components]; simp [Component.Covers]) _)
    (lodsw_down_seg_effect_step p r base)

def lodsbDownEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.reg 0 : Operand 64), mergeGPR 8 ((Operand.mem (rsi.read s) : Operand 8).read s)
      ((Operand.reg 0 : Operand 64).read s)⟩,
    ⟨rsi, rsi.read s - 1⟩]

@[simp] theorem lodsbDownEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (lodsbDownEffect p len s).components = [.reg 0, .reg 6, .rip] := by
  simp [lodsbDownEffect, Effect.components]

theorem lodsb_down_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (LodsDownPre p 1) (codeRange p [0xAC]) (lodsbDownEffect p 1) := by
  rintro s h hcode ⟨hp, hdf, hrd⟩
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := lodsb_down_step s h [] (by simp) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hrd
  exact ⟨_, hstep, ReadyToStep.afterStep_lods_down h _ _ _,
    ⟨afterStep_lods_down_rip h _ _ _, ⟨Operand.read_afterStep_lods_down_rax _ _ _ _,
      Operand.read_afterStep_lods_down_rsi _ _ _ _⟩,
      trivial,
      AgreesExcept.afterStep_lods_down _ _ _ _⟩⟩

theorem lodsb_down_triple [Bindings] (p : BitVec 64) :
    Triple (LodsDownPre p 1) (codeRange p [0xAC]) (Effect.post (lodsbDownEffect p 1)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lodsbDownEffect_components]; simp [Component.Covers]) _)
    (lodsb_down_effect_step p)

def lodsbDownSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.reg 0 : Operand 64), mergeGPR 8 ((Operand.mem (base + rsi.read s) : Operand 8).read s)
      ((Operand.reg 0 : Operand 64).read s)⟩,
    ⟨rsi, rsi.read s - 1⟩]

@[simp] theorem lodsbDownSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (s : RamState) : (lodsbDownSegEffect p len base s).components = [.reg 0, .reg 6, .rip] := by
  simp [lodsbDownSegEffect, Effect.components]

theorem lodsb_down_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    StepEffect (LodsDownSegPre p 1 r base) (codeRange p [r.prefixByte, 0xAC])
      (lodsbDownSegEffect p 2 base) := by
  rintro s h hcode ⟨hp, hdf, hrd, ⟨hseg, hbase⟩⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [] noSegPrefix_nil]
  have hstep := lodsb_down_seg_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    hdf hcode.bytesAt hlow (by rw [hsc]; exact hrd)
  rw [hsc] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_lods_down_seg h _ _ _,
    ⟨afterStep_lods_down_seg_rip h _ _ _, ⟨Operand.read_afterStep_lods_down_seg_rax _ _ _ _,
      Operand.read_afterStep_lods_down_seg_rsi _ _ _ _⟩,
      trivial,
      AgreesExcept.afterStep_lods_down_seg _ _ _ _⟩⟩

theorem lodsb_down_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (LodsDownSegPre p 1 r base) (codeRange p [r.prefixByte, 0xAC])
      (Effect.post (lodsbDownSegEffect p 2 base)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lodsbDownSegEffect_components]; simp [Component.Covers]) _)
    (lodsb_down_seg_effect_step p r base)

attribute [x86_compose] lodsqDownEffect lodsqDownSegEffect lodsdDownEffect lodsdDownSegEffect lodswDownEffect lodswDownSegEffect lodsbDownEffect lodsbDownSegEffect

@[x86_local] theorem lodsqDownEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (lodsqDownEffect p len) := by
  effect_local [lodsqDownEffect]

@[x86_local] theorem lodsqDownSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} :
    Effect.Local (lodsqDownSegEffect p len base) := by
  effect_local [lodsqDownSegEffect]

@[x86_local] theorem lodsdDownEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (lodsdDownEffect p len) := by
  effect_local [lodsdDownEffect]

@[x86_local] theorem lodsdDownSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} :
    Effect.Local (lodsdDownSegEffect p len base) := by
  effect_local [lodsdDownSegEffect]

@[x86_local] theorem lodswDownEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (lodswDownEffect p len) := by
  effect_local [lodswDownEffect]

@[x86_local] theorem lodswDownSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} :
    Effect.Local (lodswDownSegEffect p len base) := by
  effect_local [lodswDownSegEffect]

@[x86_local] theorem lodsbDownEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (lodsbDownEffect p len) := by
  effect_local [lodsbDownEffect]

@[x86_local] theorem lodsbDownSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} :
    Effect.Local (lodsbDownSegEffect p len base) := by
  effect_local [lodsbDownSegEffect]

end X86Proofs
