import X86Proofs.Instructions.Cmps.Generated.StrDown.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cmpsqDownEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s - 8⟩, ⟨rdi, rdi.read s - 8⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s) : Operand 64).read s)
    ((Operand.mem (rdi.read s) : Operand 64).read s)))

@[simp] theorem cmpsqDownEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (cmpsqDownEffect p len s).components = [.reg 6, .reg 7, .flags, .rip] := by
  simp [cmpsqDownEffect, Effect.components]

theorem cmpsq_down_effect_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (CmpsDownPre p 8) (codeRange p [rex, 0xA7]) (cmpsqDownEffect p 2) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hdf, hsrc, hdst⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := cmpsq_down_step hcm s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    hdf hcode.bytesAt hlow hsrc hdst
  exact ⟨_, hstep, ReadyToStep.afterStep_cmps_down h _ _ _,
    ⟨afterStep_cmps_down_rip h _ _ _, ⟨Operand.read_afterStep_cmps_down_rsi _ _ _ _,
      Operand.read_afterStep_cmps_down_rdi _ _ _ _⟩,
      (by
        simp only [Effect.FlagsHold, cmpsqDownEffect]
        rw [afterStep_cmps_down_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_cmps_down _ _ _ _⟩⟩

theorem cmpsq_down_triple_of_bytes [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    Triple (CmpsDownPre p 8) (codeRange p [rex, 0xA7]) (Effect.post (cmpsqDownEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpsqDownEffect_components]; simp [Component.Covers]) _)
    (cmpsq_down_effect_step hcm p rex hrex)

theorem cmpsq_down_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) :
    Triple (CmpsDownPre p 8) (codeRange p [0x48, 0xA7]) (Effect.post (cmpsqDownEffect p 2)) :=
  cmpsq_down_triple_of_bytes hcm p 0x48 (by unfold RexWPrefix; decide)

def cmpsqDownSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s - 8⟩, ⟨rdi, rdi.read s - 8⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (base + rsi.read s) : Operand 64).read s)
    ((Operand.mem (rdi.read s) : Operand 64).read s)))

@[simp] theorem cmpsqDownSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (s : RamState) : (cmpsqDownSegEffect p len base s).components = [.reg 6, .reg 7, .flags, .rip] := by
  simp [cmpsqDownSegEffect, Effect.components]

theorem cmpsq_down_seg_effect_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) (r : SegReg) (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (CmpsDownSegPre p 8 r base) (codeRange p [r.prefixByte, rex, 0xA7])
      (cmpsqDownSegEffect p 3 base) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hdf, hsrc, hdst, ⟨hseg, hbase⟩⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex] (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := cmpsq_down_seg_step hcm s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hrex.rex_w s.DS)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    hdf hcode.bytesAt hlow (by rw [hsc]; exact hsrc) hdst
  rw [hsc] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_cmps_down_seg h _ _ _,
    ⟨afterStep_cmps_down_seg_rip h _ _ _, ⟨Operand.read_afterStep_cmps_down_seg_rsi _ _ _ _,
      Operand.read_afterStep_cmps_down_seg_rdi _ _ _ _⟩,
      (by
        simp only [Effect.FlagsHold, cmpsqDownSegEffect]
        rw [afterStep_cmps_down_seg_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_cmps_down_seg _ _ _ _⟩⟩

theorem cmpsq_down_seg_triple_of_bytes [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) (r : SegReg) (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    Triple (CmpsDownSegPre p 8 r base) (codeRange p [r.prefixByte, rex, 0xA7])
      (Effect.post (cmpsqDownSegEffect p 3 base)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpsqDownSegEffect_components]; simp [Component.Covers]) _)
    (cmpsq_down_seg_effect_step hcm p r base rex hrex)

theorem cmpsq_down_seg_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (CmpsDownSegPre p 8 r base) (codeRange p [r.prefixByte, 0x48, 0xA7])
      (Effect.post (cmpsqDownSegEffect p 3 base)) :=
  cmpsq_down_seg_triple_of_bytes hcm p r base 0x48 (by unfold RexWPrefix; decide)

def cmpsdDownEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s - 4⟩, ⟨rdi, rdi.read s - 4⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s) : Operand 32).read s)
    ((Operand.mem (rdi.read s) : Operand 32).read s)))

@[simp] theorem cmpsdDownEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (cmpsdDownEffect p len s).components = [.reg 6, .reg 7, .flags, .rip] := by
  simp [cmpsdDownEffect, Effect.components]

theorem cmpsd_down_effect_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) :
    StepEffect (CmpsDownPre p 4) (codeRange p [0xA7]) (cmpsdDownEffect p 1) := by
  rintro s h hcode ⟨hp, hdf, hsrc, hdst⟩
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := cmpsd_down_step hcm s h [] (by simp) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hsrc hdst
  exact ⟨_, hstep, ReadyToStep.afterStep_cmps_down h _ _ _,
    ⟨afterStep_cmps_down_rip h _ _ _, ⟨Operand.read_afterStep_cmps_down_rsi _ _ _ _,
      Operand.read_afterStep_cmps_down_rdi _ _ _ _⟩,
      (by
        simp only [Effect.FlagsHold, cmpsdDownEffect]
        rw [afterStep_cmps_down_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_cmps_down _ _ _ _⟩⟩

theorem cmpsd_down_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) :
    Triple (CmpsDownPre p 4) (codeRange p [0xA7]) (Effect.post (cmpsdDownEffect p 1)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpsdDownEffect_components]; simp [Component.Covers]) _)
    (cmpsd_down_effect_step hcm p)

def cmpsdDownSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s - 4⟩, ⟨rdi, rdi.read s - 4⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (base + rsi.read s) : Operand 32).read s)
    ((Operand.mem (rdi.read s) : Operand 32).read s)))

@[simp] theorem cmpsdDownSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (s : RamState) : (cmpsdDownSegEffect p len base s).components = [.reg 6, .reg 7, .flags, .rip] := by
  simp [cmpsdDownSegEffect, Effect.components]

theorem cmpsd_down_seg_effect_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    StepEffect (CmpsDownSegPre p 4 r base) (codeRange p [r.prefixByte, 0xA7])
      (cmpsdDownSegEffect p 2 base) := by
  rintro s h hcode ⟨hp, hdf, hsrc, hdst, ⟨hseg, hbase⟩⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [] noSegPrefix_nil]
  have hstep := cmpsd_down_seg_step hcm s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    hdf hcode.bytesAt hlow (by rw [hsc]; exact hsrc) hdst
  rw [hsc] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_cmps_down_seg h _ _ _,
    ⟨afterStep_cmps_down_seg_rip h _ _ _, ⟨Operand.read_afterStep_cmps_down_seg_rsi _ _ _ _,
      Operand.read_afterStep_cmps_down_seg_rdi _ _ _ _⟩,
      (by
        simp only [Effect.FlagsHold, cmpsdDownSegEffect]
        rw [afterStep_cmps_down_seg_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_cmps_down_seg _ _ _ _⟩⟩

theorem cmpsd_down_seg_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (CmpsDownSegPre p 4 r base) (codeRange p [r.prefixByte, 0xA7])
      (Effect.post (cmpsdDownSegEffect p 2 base)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpsdDownSegEffect_components]; simp [Component.Covers]) _)
    (cmpsd_down_seg_effect_step hcm p r base)

def cmpswDownEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s - 2⟩, ⟨rdi, rdi.read s - 2⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s) : Operand 16).read s)
    ((Operand.mem (rdi.read s) : Operand 16).read s)))

@[simp] theorem cmpswDownEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (cmpswDownEffect p len s).components = [.reg 6, .reg 7, .flags, .rip] := by
  simp [cmpswDownEffect, Effect.components]

theorem cmpsw_down_effect_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) :
    StepEffect (CmpsDownPre p 2) (codeRange p [0x66, 0xA7]) (cmpswDownEffect p 2) := by
  rintro s h hcode ⟨hp, hdf, hsrc, hdst⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := cmpsw_down_step hcm s h [0x66] (by simpa using scanPrefix_66) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hsrc hdst
  exact ⟨_, hstep, ReadyToStep.afterStep_cmps_down h _ _ _,
    ⟨afterStep_cmps_down_rip h _ _ _, ⟨Operand.read_afterStep_cmps_down_rsi _ _ _ _,
      Operand.read_afterStep_cmps_down_rdi _ _ _ _⟩,
      (by
        simp only [Effect.FlagsHold, cmpswDownEffect]
        rw [afterStep_cmps_down_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_cmps_down _ _ _ _⟩⟩

theorem cmpsw_down_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) :
    Triple (CmpsDownPre p 2) (codeRange p [0x66, 0xA7]) (Effect.post (cmpswDownEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpswDownEffect_components]; simp [Component.Covers]) _)
    (cmpsw_down_effect_step hcm p)

def cmpswDownSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s - 2⟩, ⟨rdi, rdi.read s - 2⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (base + rsi.read s) : Operand 16).read s)
    ((Operand.mem (rdi.read s) : Operand 16).read s)))

@[simp] theorem cmpswDownSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (s : RamState) : (cmpswDownSegEffect p len base s).components = [.reg 6, .reg 7, .flags, .rip] := by
  simp [cmpswDownSegEffect, Effect.components]

theorem cmpsw_down_seg_effect_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    StepEffect (CmpsDownSegPre p 2 r base) (codeRange p [r.prefixByte, 0x66, 0xA7])
      (cmpswDownSegEffect p 3 base) := by
  rintro s h hcode ⟨hp, hdf, hsrc, hdst, ⟨hseg, hbase⟩⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66] (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil)]
  have hstep := cmpsw_down_seg_step hcm s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    hdf hcode.bytesAt hlow (by rw [hsc]; exact hsrc) hdst
  rw [hsc] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_cmps_down_seg h _ _ _,
    ⟨afterStep_cmps_down_seg_rip h _ _ _, ⟨Operand.read_afterStep_cmps_down_seg_rsi _ _ _ _,
      Operand.read_afterStep_cmps_down_seg_rdi _ _ _ _⟩,
      (by
        simp only [Effect.FlagsHold, cmpswDownSegEffect]
        rw [afterStep_cmps_down_seg_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_cmps_down_seg _ _ _ _⟩⟩

theorem cmpsw_down_seg_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (CmpsDownSegPre p 2 r base) (codeRange p [r.prefixByte, 0x66, 0xA7])
      (Effect.post (cmpswDownSegEffect p 3 base)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpswDownSegEffect_components]; simp [Component.Covers]) _)
    (cmpsw_down_seg_effect_step hcm p r base)

def cmpsbDownEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s - 1⟩, ⟨rdi, rdi.read s - 1⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s) : Operand 8).read s)
    ((Operand.mem (rdi.read s) : Operand 8).read s)))

@[simp] theorem cmpsbDownEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (cmpsbDownEffect p len s).components = [.reg 6, .reg 7, .flags, .rip] := by
  simp [cmpsbDownEffect, Effect.components]

theorem cmpsb_down_effect_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) :
    StepEffect (CmpsDownPre p 1) (codeRange p [0xA6]) (cmpsbDownEffect p 1) := by
  rintro s h hcode ⟨hp, hdf, hsrc, hdst⟩
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := cmpsb_down_step hcm s h [] (by simp) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hsrc hdst
  exact ⟨_, hstep, ReadyToStep.afterStep_cmps_down h _ _ _,
    ⟨afterStep_cmps_down_rip h _ _ _, ⟨Operand.read_afterStep_cmps_down_rsi _ _ _ _,
      Operand.read_afterStep_cmps_down_rdi _ _ _ _⟩,
      (by
        simp only [Effect.FlagsHold, cmpsbDownEffect]
        rw [afterStep_cmps_down_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_cmps_down _ _ _ _⟩⟩

theorem cmpsb_down_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) :
    Triple (CmpsDownPre p 1) (codeRange p [0xA6]) (Effect.post (cmpsbDownEffect p 1)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpsbDownEffect_components]; simp [Component.Covers]) _)
    (cmpsb_down_effect_step hcm p)

def cmpsbDownSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s - 1⟩, ⟨rdi, rdi.read s - 1⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (base + rsi.read s) : Operand 8).read s)
    ((Operand.mem (rdi.read s) : Operand 8).read s)))

@[simp] theorem cmpsbDownSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (s : RamState) : (cmpsbDownSegEffect p len base s).components = [.reg 6, .reg 7, .flags, .rip] := by
  simp [cmpsbDownSegEffect, Effect.components]

theorem cmpsb_down_seg_effect_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    StepEffect (CmpsDownSegPre p 1 r base) (codeRange p [r.prefixByte, 0xA6])
      (cmpsbDownSegEffect p 2 base) := by
  rintro s h hcode ⟨hp, hdf, hsrc, hdst, ⟨hseg, hbase⟩⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [] noSegPrefix_nil]
  have hstep := cmpsb_down_seg_step hcm s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    hdf hcode.bytesAt hlow (by rw [hsc]; exact hsrc) hdst
  rw [hsc] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_cmps_down_seg h _ _ _,
    ⟨afterStep_cmps_down_seg_rip h _ _ _, ⟨Operand.read_afterStep_cmps_down_seg_rsi _ _ _ _,
      Operand.read_afterStep_cmps_down_seg_rdi _ _ _ _⟩,
      (by
        simp only [Effect.FlagsHold, cmpsbDownSegEffect]
        rw [afterStep_cmps_down_seg_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_cmps_down_seg _ _ _ _⟩⟩

theorem cmpsb_down_seg_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (CmpsDownSegPre p 1 r base) (codeRange p [r.prefixByte, 0xA6])
      (Effect.post (cmpsbDownSegEffect p 2 base)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpsbDownSegEffect_components]; simp [Component.Covers]) _)
    (cmpsb_down_seg_effect_step hcm p r base)

attribute [x86_compose] cmpsqDownEffect cmpsqDownSegEffect cmpsdDownEffect cmpsdDownSegEffect cmpswDownEffect cmpswDownSegEffect cmpsbDownEffect cmpsbDownSegEffect

@[x86_local] theorem cmpsqDownEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (cmpsqDownEffect p len) := by
  effect_local [cmpsqDownEffect]

@[x86_local] theorem cmpsqDownSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} :
    Effect.Local (cmpsqDownSegEffect p len base) := by
  effect_local [cmpsqDownSegEffect]

@[x86_local] theorem cmpsdDownEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (cmpsdDownEffect p len) := by
  effect_local [cmpsdDownEffect]

@[x86_local] theorem cmpsdDownSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} :
    Effect.Local (cmpsdDownSegEffect p len base) := by
  effect_local [cmpsdDownSegEffect]

@[x86_local] theorem cmpswDownEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (cmpswDownEffect p len) := by
  effect_local [cmpswDownEffect]

@[x86_local] theorem cmpswDownSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} :
    Effect.Local (cmpswDownSegEffect p len base) := by
  effect_local [cmpswDownSegEffect]

@[x86_local] theorem cmpsbDownEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (cmpsbDownEffect p len) := by
  effect_local [cmpsbDownEffect]

@[x86_local] theorem cmpsbDownSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} :
    Effect.Local (cmpsbDownSegEffect p len base) := by
  effect_local [cmpsbDownSegEffect]

end X86Proofs
