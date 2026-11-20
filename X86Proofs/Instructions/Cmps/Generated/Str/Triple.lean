import X86Proofs.Instructions.Cmps.Generated.Str.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cmpsqEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s + 8⟩, ⟨rdi, rdi.read s + 8⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s) : Operand 64).read s)
    ((Operand.mem (rdi.read s) : Operand 64).read s)))

@[simp] theorem cmpsqEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (cmpsqEffect p len s).components = [.reg 6, .reg 7, .flags, .rip] := by
  simp [cmpsqEffect, Effect.components]

theorem cmpsq_effect_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (CmpsPre p 8) (codeRange p [rex, 0xA7]) (cmpsqEffect p 2) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hdf, hsrc, hdst⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := cmpsq_step hcm s h [rex] (by simpa using hr.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl)
    hdf hcode.bytesAt hlow hsrc hdst
  exact ⟨_, hstep, ReadyToStep.afterStep_cmps h _ _ _,
    ⟨afterStep_cmps_rip h _ _ _, ⟨Operand.read_afterStep_cmps_rsi _ _ _ _,
      Operand.read_afterStep_cmps_rdi _ _ _ _⟩,
      (by
        simp only [Effect.FlagsHold, cmpsqEffect]
        rw [afterStep_cmps_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_cmps _ _ _ _⟩⟩

theorem cmpsq_triple_of_bytes [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    Triple (CmpsPre p 8) (codeRange p [rex, 0xA7]) (Effect.post (cmpsqEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpsqEffect_components]; simp [Component.Covers]) _)
    (cmpsq_effect_step hcm p rex hrex)

theorem cmpsq_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) :
    Triple (CmpsPre p 8) (codeRange p [0x48, 0xA7]) (Effect.post (cmpsqEffect p 2)) :=
  cmpsq_triple_of_bytes hcm p 0x48 (by unfold RexWPrefix; decide)

def cmpsqSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s + 8⟩, ⟨rdi, rdi.read s + 8⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (base + rsi.read s) : Operand 64).read s)
    ((Operand.mem (rdi.read s) : Operand 64).read s)))

@[simp] theorem cmpsqSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (s : RamState) : (cmpsqSegEffect p len base s).components = [.reg 6, .reg 7, .flags, .rip] := by
  simp [cmpsqSegEffect, Effect.components]

theorem cmpsq_seg_effect_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) (r : SegReg) (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (CmpsSegPre p 8 r base) (codeRange p [r.prefixByte, rex, 0xA7])
      (cmpsqSegEffect p 3 base) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hdf, hsrc, hdst, ⟨hseg, hbase⟩⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex] (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := cmpsq_seg_step hcm s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
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
  exact ⟨_, hstep, ReadyToStep.afterStep_cmps_seg h _ _ _,
    ⟨afterStep_cmps_seg_rip h _ _ _, ⟨Operand.read_afterStep_cmps_seg_rsi _ _ _ _,
      Operand.read_afterStep_cmps_seg_rdi _ _ _ _⟩,
      (by
        simp only [Effect.FlagsHold, cmpsqSegEffect]
        rw [afterStep_cmps_seg_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_cmps_seg _ _ _ _⟩⟩

theorem cmpsq_seg_triple_of_bytes [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) (r : SegReg) (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    Triple (CmpsSegPre p 8 r base) (codeRange p [r.prefixByte, rex, 0xA7])
      (Effect.post (cmpsqSegEffect p 3 base)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpsqSegEffect_components]; simp [Component.Covers]) _)
    (cmpsq_seg_effect_step hcm p r base rex hrex)

theorem cmpsq_seg_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (CmpsSegPre p 8 r base) (codeRange p [r.prefixByte, 0x48, 0xA7])
      (Effect.post (cmpsqSegEffect p 3 base)) :=
  cmpsq_seg_triple_of_bytes hcm p r base 0x48 (by unfold RexWPrefix; decide)

def cmpsdEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s + 4⟩, ⟨rdi, rdi.read s + 4⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s) : Operand 32).read s)
    ((Operand.mem (rdi.read s) : Operand 32).read s)))

@[simp] theorem cmpsdEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (cmpsdEffect p len s).components = [.reg 6, .reg 7, .flags, .rip] := by
  simp [cmpsdEffect, Effect.components]

theorem cmpsd_effect_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) :
    StepEffect (CmpsPre p 4) (codeRange p [0xA7]) (cmpsdEffect p 1) := by
  rintro s h hcode ⟨hp, hdf, hsrc, hdst⟩
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := cmpsd_step hcm s h [] (by simp) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hsrc hdst
  exact ⟨_, hstep, ReadyToStep.afterStep_cmps h _ _ _,
    ⟨afterStep_cmps_rip h _ _ _, ⟨Operand.read_afterStep_cmps_rsi _ _ _ _,
      Operand.read_afterStep_cmps_rdi _ _ _ _⟩,
      (by
        simp only [Effect.FlagsHold, cmpsdEffect]
        rw [afterStep_cmps_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_cmps _ _ _ _⟩⟩

theorem cmpsd_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) :
    Triple (CmpsPre p 4) (codeRange p [0xA7]) (Effect.post (cmpsdEffect p 1)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpsdEffect_components]; simp [Component.Covers]) _)
    (cmpsd_effect_step hcm p)

def cmpsdSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s + 4⟩, ⟨rdi, rdi.read s + 4⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (base + rsi.read s) : Operand 32).read s)
    ((Operand.mem (rdi.read s) : Operand 32).read s)))

@[simp] theorem cmpsdSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (s : RamState) : (cmpsdSegEffect p len base s).components = [.reg 6, .reg 7, .flags, .rip] := by
  simp [cmpsdSegEffect, Effect.components]

theorem cmpsd_seg_effect_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    StepEffect (CmpsSegPre p 4 r base) (codeRange p [r.prefixByte, 0xA7])
      (cmpsdSegEffect p 2 base) := by
  rintro s h hcode ⟨hp, hdf, hsrc, hdst, ⟨hseg, hbase⟩⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [] noSegPrefix_nil]
  have hstep := cmpsd_seg_step hcm s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
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
  exact ⟨_, hstep, ReadyToStep.afterStep_cmps_seg h _ _ _,
    ⟨afterStep_cmps_seg_rip h _ _ _, ⟨Operand.read_afterStep_cmps_seg_rsi _ _ _ _,
      Operand.read_afterStep_cmps_seg_rdi _ _ _ _⟩,
      (by
        simp only [Effect.FlagsHold, cmpsdSegEffect]
        rw [afterStep_cmps_seg_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_cmps_seg _ _ _ _⟩⟩

theorem cmpsd_seg_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (CmpsSegPre p 4 r base) (codeRange p [r.prefixByte, 0xA7])
      (Effect.post (cmpsdSegEffect p 2 base)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpsdSegEffect_components]; simp [Component.Covers]) _)
    (cmpsd_seg_effect_step hcm p r base)

def cmpswEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s + 2⟩, ⟨rdi, rdi.read s + 2⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s) : Operand 16).read s)
    ((Operand.mem (rdi.read s) : Operand 16).read s)))

@[simp] theorem cmpswEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (cmpswEffect p len s).components = [.reg 6, .reg 7, .flags, .rip] := by
  simp [cmpswEffect, Effect.components]

theorem cmpsw_effect_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) :
    StepEffect (CmpsPre p 2) (codeRange p [0x66, 0xA7]) (cmpswEffect p 2) := by
  rintro s h hcode ⟨hp, hdf, hsrc, hdst⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := cmpsw_step hcm s h [0x66] (by simpa using scanPrefix_66) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hsrc hdst
  exact ⟨_, hstep, ReadyToStep.afterStep_cmps h _ _ _,
    ⟨afterStep_cmps_rip h _ _ _, ⟨Operand.read_afterStep_cmps_rsi _ _ _ _,
      Operand.read_afterStep_cmps_rdi _ _ _ _⟩,
      (by
        simp only [Effect.FlagsHold, cmpswEffect]
        rw [afterStep_cmps_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_cmps _ _ _ _⟩⟩

theorem cmpsw_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) :
    Triple (CmpsPre p 2) (codeRange p [0x66, 0xA7]) (Effect.post (cmpswEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpswEffect_components]; simp [Component.Covers]) _)
    (cmpsw_effect_step hcm p)

def cmpswSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s + 2⟩, ⟨rdi, rdi.read s + 2⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (base + rsi.read s) : Operand 16).read s)
    ((Operand.mem (rdi.read s) : Operand 16).read s)))

@[simp] theorem cmpswSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (s : RamState) : (cmpswSegEffect p len base s).components = [.reg 6, .reg 7, .flags, .rip] := by
  simp [cmpswSegEffect, Effect.components]

theorem cmpsw_seg_effect_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    StepEffect (CmpsSegPre p 2 r base) (codeRange p [r.prefixByte, 0x66, 0xA7])
      (cmpswSegEffect p 3 base) := by
  rintro s h hcode ⟨hp, hdf, hsrc, hdst, ⟨hseg, hbase⟩⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66] (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil)]
  have hstep := cmpsw_seg_step hcm s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
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
  exact ⟨_, hstep, ReadyToStep.afterStep_cmps_seg h _ _ _,
    ⟨afterStep_cmps_seg_rip h _ _ _, ⟨Operand.read_afterStep_cmps_seg_rsi _ _ _ _,
      Operand.read_afterStep_cmps_seg_rdi _ _ _ _⟩,
      (by
        simp only [Effect.FlagsHold, cmpswSegEffect]
        rw [afterStep_cmps_seg_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_cmps_seg _ _ _ _⟩⟩

theorem cmpsw_seg_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (CmpsSegPre p 2 r base) (codeRange p [r.prefixByte, 0x66, 0xA7])
      (Effect.post (cmpswSegEffect p 3 base)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpswSegEffect_components]; simp [Component.Covers]) _)
    (cmpsw_seg_effect_step hcm p r base)

def cmpsbEffect (p : BitVec 64) (len : Nat) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s + 1⟩, ⟨rdi, rdi.read s + 1⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (rsi.read s) : Operand 8).read s)
    ((Operand.mem (rdi.read s) : Operand 8).read s)))

@[simp] theorem cmpsbEffect_components (p : BitVec 64) (len : Nat) (s : RamState) :
    (cmpsbEffect p len s).components = [.reg 6, .reg 7, .flags, .rip] := by
  simp [cmpsbEffect, Effect.components]

theorem cmpsb_effect_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) :
    StepEffect (CmpsPre p 1) (codeRange p [0xA6]) (cmpsbEffect p 1) := by
  rintro s h hcode ⟨hp, hdf, hsrc, hdst⟩
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := cmpsb_step hcm s h [] (by simp) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    hdf hcode.bytesAt hlow hsrc hdst
  exact ⟨_, hstep, ReadyToStep.afterStep_cmps h _ _ _,
    ⟨afterStep_cmps_rip h _ _ _, ⟨Operand.read_afterStep_cmps_rsi _ _ _ _,
      Operand.read_afterStep_cmps_rdi _ _ _ _⟩,
      (by
        simp only [Effect.FlagsHold, cmpsbEffect]
        rw [afterStep_cmps_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_cmps _ _ _ _⟩⟩

theorem cmpsb_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) :
    Triple (CmpsPre p 1) (codeRange p [0xA6]) (Effect.post (cmpsbEffect p 1)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpsbEffect_components]; simp [Component.Covers]) _)
    (cmpsb_effect_step hcm p)

def cmpsbSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨rsi, rsi.read s + 1⟩, ⟨rdi, rdi.read s + 1⟩]
  flags := some (.ofStatusFlags (cmpSpec ((Operand.mem (base + rsi.read s) : Operand 8).read s)
    ((Operand.mem (rdi.read s) : Operand 8).read s)))

@[simp] theorem cmpsbSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (s : RamState) : (cmpsbSegEffect p len base s).components = [.reg 6, .reg 7, .flags, .rip] := by
  simp [cmpsbSegEffect, Effect.components]

theorem cmpsb_seg_effect_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    StepEffect (CmpsSegPre p 1 r base) (codeRange p [r.prefixByte, 0xA6])
      (cmpsbSegEffect p 2 base) := by
  rintro s h hcode ⟨hp, hdf, hsrc, hdst, ⟨hseg, hbase⟩⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [] noSegPrefix_nil]
  have hstep := cmpsb_seg_step hcm s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl)
    (by rw [hsc]; exact hseg)
    hdf hcode.bytesAt hlow (by rw [hsc]; exact hsrc) hdst
  rw [hsc] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_cmps_seg h _ _ _,
    ⟨afterStep_cmps_seg_rip h _ _ _, ⟨Operand.read_afterStep_cmps_seg_rsi _ _ _ _,
      Operand.read_afterStep_cmps_seg_rdi _ _ _ _⟩,
      (by
        simp only [Effect.FlagsHold, cmpsbSegEffect]
        rw [afterStep_cmps_seg_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_cmps_seg _ _ _ _⟩⟩

theorem cmpsb_seg_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) (r : SegReg) (base : BitVec 64) :
    Triple (CmpsSegPre p 1 r base) (codeRange p [r.prefixByte, 0xA6])
      (Effect.post (cmpsbSegEffect p 2 base)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpsbSegEffect_components]; simp [Component.Covers]) _)
    (cmpsb_seg_effect_step hcm p r base)

theorem cmpsq_a32_effect_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    StepEffect (fun s => CmpsPre p 8 s ∧ (rsi.read s).toNat + 8 < 2^32 ∧ (rdi.read s).toNat + 8 < 2^32) (codeRange p [0x67, rex, 0xA7])
      (cmpsqEffect p 3) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨⟨hp, hdf, hsrc, hdst⟩, hsl, hdl⟩
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := cmpsq_a32_step hcm s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; exact hrex.rex_w s.DS)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_asz_cons, scanContext_rex _ _ hr]; rfl)
    hdf hcode.bytesAt hlow hsrc hdst hsl hdl
  exact ⟨_, hstep, ReadyToStep.afterStep_cmps h _ _ _,
    ⟨afterStep_cmps_rip h _ _ _, ⟨Operand.read_afterStep_cmps_rsi _ _ _ _,
      Operand.read_afterStep_cmps_rdi _ _ _ _⟩,
      (by
        simp only [Effect.FlagsHold, cmpsqEffect]
        rw [afterStep_cmps_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_cmps _ _ _ _⟩⟩

theorem cmpsq_a32_triple_of_bytes [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) :
    Triple (fun s => CmpsPre p 8 s ∧ (rsi.read s).toNat + 8 < 2^32 ∧ (rdi.read s).toNat + 8 < 2^32) (codeRange p [0x67, rex, 0xA7])
      (Effect.post (cmpsqEffect p 3)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpsqEffect_components]; simp [Component.Covers]) _)
    (cmpsq_a32_effect_step hcm p rex hrex)

theorem cmpsq_a32_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) :
    Triple (fun s => CmpsPre p 8 s ∧ (rsi.read s).toNat + 8 < 2^32 ∧ (rdi.read s).toNat + 8 < 2^32) (codeRange p [0x67, 0x48, 0xA7])
      (Effect.post (cmpsqEffect p 3)) :=
  cmpsq_a32_triple_of_bytes hcm p 0x48 (by unfold RexWPrefix; decide)

theorem cmpsd_a32_effect_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) :
    StepEffect (fun s => CmpsPre p 4 s ∧ (rsi.read s).toNat + 4 < 2^32 ∧ (rdi.read s).toNat + 4 < 2^32) (codeRange p [0x67, 0xA7])
      (cmpsdEffect p 2) := by
  rintro s h hcode ⟨⟨hp, hdf, hsrc, hdst⟩, hsl, hdl⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := cmpsd_a32_step hcm s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    hdf hcode.bytesAt hlow hsrc hdst hsl hdl
  exact ⟨_, hstep, ReadyToStep.afterStep_cmps h _ _ _,
    ⟨afterStep_cmps_rip h _ _ _, ⟨Operand.read_afterStep_cmps_rsi _ _ _ _,
      Operand.read_afterStep_cmps_rdi _ _ _ _⟩,
      (by
        simp only [Effect.FlagsHold, cmpsdEffect]
        rw [afterStep_cmps_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_cmps _ _ _ _⟩⟩

theorem cmpsd_a32_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) :
    Triple (fun s => CmpsPre p 4 s ∧ (rsi.read s).toNat + 4 < 2^32 ∧ (rdi.read s).toNat + 4 < 2^32) (codeRange p [0x67, 0xA7])
      (Effect.post (cmpsdEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpsdEffect_components]; simp [Component.Covers]) _)
    (cmpsd_a32_effect_step hcm p)

theorem cmpsw_a32_effect_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) :
    StepEffect (fun s => CmpsPre p 2 s ∧ (rsi.read s).toNat + 2 < 2^32 ∧ (rdi.read s).toNat + 2 < 2^32) (codeRange p [0x67, 0x66, 0xA7])
      (cmpswEffect p 3) := by
  rintro s h hcode ⟨⟨hp, hdf, hsrc, hdst⟩, hsl, hdl⟩
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := cmpsw_a32_step hcm s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    hdf hcode.bytesAt hlow hsrc hdst hsl hdl
  exact ⟨_, hstep, ReadyToStep.afterStep_cmps h _ _ _,
    ⟨afterStep_cmps_rip h _ _ _, ⟨Operand.read_afterStep_cmps_rsi _ _ _ _,
      Operand.read_afterStep_cmps_rdi _ _ _ _⟩,
      (by
        simp only [Effect.FlagsHold, cmpswEffect]
        rw [afterStep_cmps_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_cmps _ _ _ _⟩⟩

theorem cmpsw_a32_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) :
    Triple (fun s => CmpsPre p 2 s ∧ (rsi.read s).toNat + 2 < 2^32 ∧ (rdi.read s).toNat + 2 < 2^32) (codeRange p [0x67, 0x66, 0xA7])
      (Effect.post (cmpswEffect p 3)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpswEffect_components]; simp [Component.Covers]) _)
    (cmpsw_a32_effect_step hcm p)

theorem cmpsb_a32_effect_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) :
    StepEffect (fun s => CmpsPre p 1 s ∧ (rsi.read s).toNat + 1 < 2^32 ∧ (rdi.read s).toNat + 1 < 2^32) (codeRange p [0x67, 0xA6])
      (cmpsbEffect p 2) := by
  rintro s h hcode ⟨⟨hp, hdf, hsrc, hdst⟩, hsl, hdl⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  have hstep := cmpsb_a32_step hcm s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    (by rw [scanContext_asz_cons]; rfl)
    hdf hcode.bytesAt hlow hsrc hdst hsl hdl
  exact ⟨_, hstep, ReadyToStep.afterStep_cmps h _ _ _,
    ⟨afterStep_cmps_rip h _ _ _, ⟨Operand.read_afterStep_cmps_rsi _ _ _ _,
      Operand.read_afterStep_cmps_rdi _ _ _ _⟩,
      (by
        simp only [Effect.FlagsHold, cmpsbEffect]
        rw [afterStep_cmps_rflags]
        exact StatusFlagsOutcome.allows_store (StatusFlagsOutcome.allows_ofStatusFlags _) _),
      AgreesExcept.afterStep_cmps _ _ _ _⟩⟩

theorem cmpsb_a32_triple [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram))) (p : BitVec 64) :
    Triple (fun s => CmpsPre p 1 s ∧ (rsi.read s).toNat + 1 < 2^32 ∧ (rdi.read s).toNat + 1 < 2^32) (codeRange p [0x67, 0xA6])
      (Effect.post (cmpsbEffect p 2)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [cmpsbEffect_components]; simp [Component.Covers]) _)
    (cmpsb_a32_effect_step hcm p)

attribute [x86_compose] cmpsqEffect cmpsqSegEffect cmpsdEffect cmpsdSegEffect cmpswEffect cmpswSegEffect cmpsbEffect cmpsbSegEffect

@[x86_local] theorem cmpsqEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (cmpsqEffect p len) := by
  effect_local [cmpsqEffect]

@[x86_local] theorem cmpsqSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} :
    Effect.Local (cmpsqSegEffect p len base) := by
  effect_local [cmpsqSegEffect]

@[x86_local] theorem cmpsdEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (cmpsdEffect p len) := by
  effect_local [cmpsdEffect]

@[x86_local] theorem cmpsdSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} :
    Effect.Local (cmpsdSegEffect p len base) := by
  effect_local [cmpsdSegEffect]

@[x86_local] theorem cmpswEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (cmpswEffect p len) := by
  effect_local [cmpswEffect]

@[x86_local] theorem cmpswSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} :
    Effect.Local (cmpswSegEffect p len base) := by
  effect_local [cmpswSegEffect]

@[x86_local] theorem cmpsbEffect_local {p : BitVec 64} {len : Nat} :
    Effect.Local (cmpsbEffect p len) := by
  effect_local [cmpsbEffect]

@[x86_local] theorem cmpsbSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} :
    Effect.Local (cmpsbSegEffect p len base) := by
  effect_local [cmpsbSegEffect]

end X86Proofs
