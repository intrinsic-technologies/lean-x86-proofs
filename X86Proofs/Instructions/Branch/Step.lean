import X86Proofs.Step.AfterStep
import X86Proofs.Program.Agrees
import X86Proofs.Instructions.Branch.Decode
import X86Proofs.Instructions.Nop.Step
import X86Proofs.Instructions.Loop.Operation
import X86Proofs.Program.ReadWrite.WriteResult

/-!
# Layer 3: relative branch step theorems

One step theorem per encoding, each with result
`afterStep s len fun t => branchState t taken (RIP + len) (RIP + len + sext disp)`:

- `jcc_rel8_step`: `70+cc rel8` (2 bytes), taken iff `condHolds cc` of the flags;
- `jcc_rel32_step`: `0F 80+cc rel32` (6 bytes), the same through the `0F` escape;
- `jmp_rel8_step`: `EB rel8` (2 bytes), always taken;
- `jmp_rel32_step`: `E9 rel32` (5 bytes), always taken.

The condition is stated on the flags of the start state `s` (the housekeeping before the form
does not touch RFLAGS). A taken branch needs its target below 4 GiB (`htarget`; for `Jcc` only
when the condition holds).

What a step whose form ends in `branchState` preserves (for any length): `afterStep_branchState_rip`,
`ReadyToStep.afterStep_branchState`, `AgreesExcept.afterStep_branchState` (only RIP changes). The
same for a `LOOP` step (`loopState`, for the generated `Instructions/{Loop,Loope,Loopne}`):
`afterStep_loop_rip`, `Operand.read_afterStep_loop_rcx`, `AgreesExcept.afterStep_loop` (RCX and
RIP), `ReadyToStep.afterStep_loop`; at address size 32 (`loop32State`) the same with `loop32`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- The `Jcc rel8` opcode for condition `cc`: `70 + cc`. -/
def jccOpcode8 (cc : BitVec 4) : UInt8 := UInt8.ofNat (0x70 + cc.toNat)

/-- The second byte of the `Jcc rel32` opcode for condition `cc`: `0F (80 + cc)`. -/
def jccOpcode32 (cc : BitVec 4) : UInt8 := UInt8.ofNat (0x80 + cc.toNat)

theorem jccOpcode8_mem (cc : BitVec 4) : (jccOpcode8 cc).toBitVec ∈ jccOpcodes8 := by
  revert cc
  decide

theorem jccOpcode32_mem (cc : BitVec 4) : (jccOpcode32 cc).toBitVec ∈ jccOpcodes32 := by
  revert cc
  decide

theorem jccOpcode8_cc (cc : BitVec 4) : (jccOpcode8 cc).toBitVec.extractLsb' 0 4 = cc := by
  revert cc
  decide

theorem jccOpcode32_cc (cc : BitVec 4) : (jccOpcode32 cc).toBitVec.extractLsb' 0 4 = cc := by
  revert cc
  decide

theorem jccOpcode8_legacyOpcode (cc : BitVec 4) : LegacyOpcode (jccOpcode8 cc).toBitVec := by
  apply legacyOpcode_of_check
  revert cc
  decide

theorem jccOpcode32_ne (cc : BitVec 4) : jccOpcode32 cc ≠ 0x38 ∧ jccOpcode32 cc ≠ 0x3A := by
  revert cc
  decide

/-- The facts a taken branch's checks need hold on the state the form runs in. -/
theorem ReadyToStep.branchReady [Bindings] {s : RamState} (h : ReadyToStep s) (k : Nat) :
    BranchReady (afterFetches (beforeFetch s) k) :=
  ⟨h.cpu.cs, h.cpu.efer.lma, h.cpu.cpl, h.cpu.cr0, h.cpu.cr4, h.fetchReady.efer.lme,
    reportsCPUFeature_of_sameControls (s := s) (t := afterFetches (beforeFetch s) k) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.cpu.lam⟩

/-- After a form that ends in `branchState`, RIP is the target if taken, else `nextIP`. -/
theorem afterStep_branchState_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (taken : Bool) (nextIP target : BitVec 64) :
    (afterStep s length fun t => branchState t taken nextIP target).RIP =
      if taken then target else nextIP := by
  cases taken <;>
  simp [afterStep, finishStep, branchState, jumpState, withNextIP, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- Preservation: after a form that ends in `branchState`, the state is ready to step again. -/
theorem ReadyToStep.afterStep_branchState [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (taken : Bool) (nextIP target : BitVec 64) :
    ReadyToStep (afterStep s length fun t => branchState t taken nextIP target) := by
  cases taken
  · exact ReadyToStep.afterStep_withNextIP h length nextIP
  · have hst : SameControls s (afterStep s length fun t => branchState t true nextIP target) :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hc := h.cpu
    have hr := h.ready
    exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical,
        hc.early, reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass,
        hc.debug, hc.aet⟩,
      ⟨h.memory.cr3, h.memory.tables⟩,
      ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
        hr.busLock, hr.tf, hr.rf, hr.repeatClear, hr.msr⟩,
      smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
      h.features.of_sameControls hst⟩

/-- A step whose form ends in `branchState` changes only RIP (besides the per-step
bookkeeping, which includes `Branch_Taken`). -/
theorem AgreesExcept.afterStep_branchState (s : RamState) (length : Nat) (taken : Bool)
    (nextIP target : BitVec 64) :
    AgreesExcept [.rip] s (afterStep s length fun t => branchState t taken nextIP target) := by
  cases taken
  · exact AgreesExcept.afterStep_withNextIP s length nextIP
  · refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
    · cases c with
      | reg r => rfl
      | flags => rfl
      | rip => exact absurd (by simp) hc
      | mem addr len => exact fun _ _ => rfl
      | xmm x => exact Component.agrees_xmm_of_zmm rfl x
      | mxcsr => rfl
      | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
      | fsw => rfl
      | fcc => rfl
      | ftw => rfl
      | fcw => rfl
      | fpuPtr => rfl
      | df => rfl
    · simp only [fixedPart, afterStep, finishStep, branchState, jumpState, afterFetches,
        beforeFetch, resetStepFields, ite_true]

/-! ### After a LOOP step -/

/-- After a `LOOP` step (`loopState`, `Instructions/Loop/Operation.lean`), RIP is the target if
the branch is taken, else `nextIP`. -/
theorem afterStep_loop_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (taken : Bool) (nextIP target : BitVec 64) :
    (afterStep s length fun t => loopState (withNextIP t nextIP) taken target).RIP =
      if taken then target else nextIP := by
  cases taken <;>
  simp [afterStep, finishStep, loopState, Operand.write, withNextIP, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- After a `LOOP` step, RCX is the old RCX - 1. -/
theorem Operand.read_afterStep_loop_rcx (s : RamState) (length : Nat) (taken : Bool)
    (nextIP target : BitVec 64) :
    rcx.read (afterStep s length fun t => loopState (withNextIP t nextIP) taken target) =
      rcx.read s - 1 := by
  rw [Operand.read_afterStep, loopState, rcx_read_write]
  cases taken <;> rfl

/-- A `LOOP` step changes only RCX and RIP (besides the bookkeeping). -/
theorem AgreesExcept.afterStep_loop (s : RamState) (length : Nat) (taken : Bool)
    (nextIP target : BitVec 64) :
    AgreesExcept [.reg 1, .rip] s
      (afterStep s length fun t => loopState (withNextIP t nextIP) taken target) := by
  cases taken
  · exact AgreesExcept.afterStep_writeResult s length 1 (fun t => rcx.read t - 1) nextIP
  · refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
    · cases c with
      | reg r =>
        have h1 : (1 : BitVec 5) ≠ r := fun h => hc (h ▸ List.mem_cons_self)
        have := Operand.read_write_reg_of_ne (m := 64)
          (jumpState (afterFetches (beforeFetch s) (length + 1)) nextIP target) h1
          (rcx.read s - 1)
        simp only [Operand.read_reg64] at this
        exact this
      | flags => rfl
      | rip => exact absurd (by simp) hc
      | mem addr len => exact fun _ _ => rfl
      | xmm x => exact Component.agrees_xmm_of_zmm rfl x
      | mxcsr => rfl
      | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
      | fsw => rfl
      | fcc => rfl
      | ftw => rfl
      | fcw => rfl
      | fpuPtr => rfl
      | df => rfl
    · simp only [fixedPart, afterStep, finishStep, loopState, Operand.write, withNextIP,
        afterFetches, beforeFetch, resetStepFields, ↓reduceIte]

/-- Preservation for a `LOOP` step. -/
theorem ReadyToStep.afterStep_loop [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (taken : Bool) (nextIP target : BitVec 64) :
    ReadyToStep (afterStep s length fun t => loopState (withNextIP t nextIP) taken target) :=
  h.of_agreesExcept (AgreesExcept.afterStep_loop s length taken nextIP target)
    (by cases taken <;> exact h.memory.tables)

/-- `afterStep_loop_rip` at address size 32 (`loop32State`). -/
theorem afterStep_loop32_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (taken : Bool) (nextIP target : BitVec 64) :
    (afterStep s length fun t => loop32State (withNextIP t nextIP) taken target).RIP =
      if taken then target else nextIP := by
  cases taken <;>
  simp [afterStep, finishStep, loop32State, Operand.write, withNextIP, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- After a `LOOP` step at address size 32, RCX is `loopCount32` of the start state. -/
theorem Operand.read_afterStep_loop32_rcx (s : RamState) (length : Nat) (taken : Bool)
    (nextIP target : BitVec 64) :
    rcx.read (afterStep s length fun t => loop32State (withNextIP t nextIP) taken target) =
      loopCount32 s := by
  rw [Operand.read_afterStep, loop32State, rcx_read_write]
  cases taken <;> rfl

/-- A `LOOP` step at address size 32 changes only RCX and RIP (besides the bookkeeping). -/
theorem AgreesExcept.afterStep_loop32 (s : RamState) (length : Nat) (taken : Bool)
    (nextIP target : BitVec 64) :
    AgreesExcept [.reg 1, .rip] s
      (afterStep s length fun t => loop32State (withNextIP t nextIP) taken target) := by
  cases taken
  · exact AgreesExcept.afterStep_writeResult s length 1 (fun t => loopCount32 t) nextIP
  · refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
    · cases c with
      | reg r =>
        have h1 : (1 : BitVec 5) ≠ r := fun h => hc (h ▸ List.mem_cons_self)
        have := Operand.read_write_reg_of_ne (m := 64)
          (jumpState (afterFetches (beforeFetch s) (length + 1)) nextIP target) h1
          (loopCount32 s)
        simp only [Operand.read_reg64] at this
        exact this
      | flags => rfl
      | rip => exact absurd (by simp) hc
      | mem addr len => exact fun _ _ => rfl
      | xmm x => exact Component.agrees_xmm_of_zmm rfl x
      | mxcsr => rfl
      | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
      | fsw => rfl
      | fcc => rfl
      | ftw => rfl
      | fcw => rfl
      | fpuPtr => rfl
      | df => rfl
    · simp only [fixedPart, afterStep, finishStep, loop32State, Operand.write, withNextIP,
        afterFetches, beforeFetch, resetStepFields, ↓reduceIte]

/-- Preservation for a `LOOP` step at address size 32. -/
theorem ReadyToStep.afterStep_loop32 [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (taken : Bool) (nextIP target : BitVec 64) :
    ReadyToStep (afterStep s length fun t => loop32State (withNextIP t nextIP) taken target) :=
  h.of_agreesExcept (AgreesExcept.afterStep_loop32 s length taken nextIP target)
    (by cases taken <;> exact h.memory.tables)

/--
Layer 3 for `jcc rel8` (`70+cc`, displacement `disp`): one `step` sets RIP to RIP + 2 + sext disp
if `condHolds cc` of the flags, else to RIP + 2.
-/
theorem jcc_rel8_step [Bindings] (s : RamState) (h : ReadyToStep s) (cc : BitVec 4)
    (disp : BitVec 8) (hcode : BytesAt s s.RIP (jccOpcode8 cc :: immBytes 8 disp))
    (hlow : s.RIP.toNat + 2 ≤ 2^32)
    (htarget : condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = true →
      (BitVec.add (BitVec.add s.RIP 2#64) (disp.signExtend 64)).toNat < 2^32) :
    X86.Machine.step s = some (.next (afterStep s 2 fun t =>
      branchState t (condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS)) (BitVec.add s.RIP 2#64)
        (BitVec.add (BitVec.add s.RIP 2#64) (disp.signExtend 64)))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (jccOpcode8 cc :: immBytes 8 disp) :=
    hcode
  have hlow' : s.RIP.toNat + (jccOpcode8 cc :: immBytes 8 disp).length ≤ 2^32 := by
    simpa using hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures (k : Nat) : DecoderFeatures (afterFetches (beforeFetch s) k) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok (jccOpcode8 cc).toBitVec, afterFetches (beforeFetch s) 2) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) 1 hf hc hlow' 0 (by simp) (by simp)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at this
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok disp, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt_imm (beforeFetch s) 2 hf hc hlow' 8 (by decide) disp 1
      (immBytes_getElem?_append [jccOpcode8 cc] disp) (by simp) (by decide)
  have hdecode := decodeLegacy0_run_of_jccOpcode8 _ _ _ (legacyContext s.DS) rfl _ (jccOpcode8_mem cc) f1
    (hmode 2)
  rw [decodeLegacy0Opcode70_run_of_jcc _ _ _ _ (hmode 2) (hfeatures 2)] at hdecode
  rw [jcc_rel8_form _ _ _ _ _ disp rfl rfl f2 (hmode 3) (h.branchReady 3)
    (by rw [jccOpcode8_cc, add_ofNat_add]; exact htarget), jccOpcode8_cc,
    add_ofNat_add] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [branchState]; split <;> exact h.ready.repeatClear)
  exact step_none_legacy0 s _ h _ (immBytes 8 disp) (jccOpcode8_legacyOpcode cc) hcode hlow' hdecode
    ((hmode 3).of_cs_lma_eq (branchState_CS _ _ _ _) (by rw [branchState_IA32_EFER]))

/--
Layer 3 for `jcc rel32` (`0F 80+cc`, displacement `disp`): one `step` sets RIP to
RIP + 6 + sext disp if `condHolds cc` of the flags, else to RIP + 6.
-/
theorem jcc_rel32_step [Bindings] (s : RamState) (h : ReadyToStep s) (cc : BitVec 4)
    (disp : BitVec 32) (hcode : BytesAt s s.RIP (0x0F :: jccOpcode32 cc :: immBytes 32 disp))
    (hlow : s.RIP.toNat + 6 ≤ 2^32)
    (htarget : condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = true →
      (BitVec.add (BitVec.add s.RIP 6#64) (disp.signExtend 64)).toNat < 2^32) :
    X86.Machine.step s = some (.next (afterStep s 6 fun t =>
      branchState t (condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS)) (BitVec.add s.RIP 6#64)
        (BitVec.add (BitVec.add s.RIP 6#64) (disp.signExtend 64)))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (0x0F :: jccOpcode32 cc :: immBytes 32 disp) := hcode
  have hlow' : s.RIP.toNat + (0x0F :: jccOpcode32 cc :: immBytes 32 disp).length ≤ 2^32 := by
    simpa using hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures (k : Nat) : DecoderFeatures (afterFetches (beforeFetch s) k) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok (jccOpcode32 cc).toBitVec, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow' 1 (by simp) (by simp)
  have f3 : (Mem_Fetch (BitVec.add (BitVec.add s.RIP 1#64) 1#64) 32).run
      (afterFetches (beforeFetch s) 3) = (.ok disp, afterFetches (beforeFetch s) 7) := by
    rw [show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc s.RIP 1#64 1#64]
    exact memFetch_run_of_bytesAt_imm (beforeFetch s) 3 hf hc hlow' 32 (by decide) disp 2
      (immBytes_getElem?_append [0x0F, jccOpcode32 cc] disp) (by simp) (by decide)
  have hdecode := decodeLegacy1_run_of_jccOpcode32 _ _ _ (legacyContext s.DS) rfl (hmode 3) _
    (jccOpcode32_mem cc) f2
  rw [decodeLegacy1Opcode80_run_of_jcc _ _ _ _ (hmode 3) (hfeatures 3)] at hdecode
  have hip : BitVec.add (BitVec.add (BitVec.add s.RIP 1#64) 1#64) 4#64 = BitVec.add s.RIP 6#64 :=
    (congrArg (BitVec.add · 4#64) (add_ofNat_add s.RIP 1 1)).trans (add_ofNat_add s.RIP 2 4)
  rw [jcc_rel32_form _ _ _ _ _ disp rfl rfl f3 (hmode 7) (h.branchReady 7)
    (by rw [jccOpcode32_cc, hip]; exact htarget), jccOpcode32_cc, hip] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [branchState]; split <;> exact h.ready.repeatClear)
  exact step_none_legacy1 s _ h _ (immBytes 32 disp) (jccOpcode32_ne cc) hcode hlow' hdecode
    ((hmode 7).of_cs_lma_eq (branchState_CS _ _ _ _) (by rw [branchState_IA32_EFER]))

/-- Layer 3 for `jmp rel8` (`EB`, displacement `disp`): one `step` sets RIP to
RIP + 2 + sext disp. -/
theorem jmp_rel8_step [Bindings] (s : RamState) (h : ReadyToStep s) (disp : BitVec 8)
    (hcode : BytesAt s s.RIP (0xEB :: immBytes 8 disp)) (hlow : s.RIP.toNat + 2 ≤ 2^32)
    (htarget : (BitVec.add (BitVec.add s.RIP 2#64) (disp.signExtend 64)).toNat < 2^32) :
    X86.Machine.step s = some (.next (afterStep s 2 fun t =>
      branchState t true (BitVec.add s.RIP 2#64)
        (BitVec.add (BitVec.add s.RIP 2#64) (disp.signExtend 64)))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0xEB :: immBytes 8 disp) := hcode
  have hlow' : s.RIP.toNat + (0xEB :: immBytes 8 disp).length ≤ 2^32 := by
    simpa using hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures (k : Nat) : DecoderFeatures (afterFetches (beforeFetch s) k) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0xEB, afterFetches (beforeFetch s) 2) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) 1 hf hc hlow' 0 (by simp) (by simp)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at this
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok disp, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt_imm (beforeFetch s) 2 hf hc hlow' 8 (by decide) disp 1
      (immBytes_getElem?_append [0xEB] disp) (by simp) (by decide)
  have hdecode := decodeLegacy0_run_of_opcodeEB _ _ _ (legacyContext s.DS) rfl f1 (hmode 2)
  rw [decodeLegacy0OpcodeEB_run_of_jmp _ _ _ (hmode 2) (hfeatures 2)] at hdecode
  rw [jmp_rel8_form _ _ _ _ disp rfl rfl f2 (hmode 3) (h.branchReady 3)
    (by rw [add_ofNat_add]; exact htarget), add_ofNat_add] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [branchState]; split <;> exact h.ready.repeatClear)
  exact step_none_legacy0 s _ h _ (immBytes 8 disp) (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    hcode hlow' hdecode ((hmode 3).of_cs_lma_eq rfl rfl)

/-- Layer 3 for `jmp rel32` (`E9`, displacement `disp`): one `step` sets RIP to
RIP + 5 + sext disp. -/
theorem jmp_rel32_step [Bindings] (s : RamState) (h : ReadyToStep s) (disp : BitVec 32)
    (hcode : BytesAt s s.RIP (0xE9 :: immBytes 32 disp)) (hlow : s.RIP.toNat + 5 ≤ 2^32)
    (htarget : (BitVec.add (BitVec.add s.RIP 5#64) (disp.signExtend 64)).toNat < 2^32) :
    X86.Machine.step s = some (.next (afterStep s 5 fun t =>
      branchState t true (BitVec.add s.RIP 5#64)
        (BitVec.add (BitVec.add s.RIP 5#64) (disp.signExtend 64)))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0xE9 :: immBytes 32 disp) := hcode
  have hlow' : s.RIP.toNat + (0xE9 :: immBytes 32 disp).length ≤ 2^32 := by
    simpa using hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures (k : Nat) : DecoderFeatures (afterFetches (beforeFetch s) k) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0xE9, afterFetches (beforeFetch s) 2) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) 1 hf hc hlow' 0 (by simp) (by simp)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at this
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 32).run (afterFetches (beforeFetch s) 2) =
      (.ok disp, afterFetches (beforeFetch s) 6) :=
    memFetch_run_of_bytesAt_imm (beforeFetch s) 2 hf hc hlow' 32 (by decide) disp 1
      (immBytes_getElem?_append [0xE9] disp) (by simp) (by decide)
  have hdecode := decodeLegacy0_run_of_opcodeE9 _ _ _ (legacyContext s.DS) rfl f1 (hmode 2)
  rw [decodeLegacy0OpcodeE9_run_of_jmp _ _ _ (hmode 2) (hfeatures 2)] at hdecode
  rw [jmp_rel32_form _ _ _ _ disp rfl rfl f2 (hmode 6) (h.branchReady 6)
    (by rw [add_ofNat_add]; exact htarget), add_ofNat_add] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [branchState]; split <;> exact h.ready.repeatClear)
  exact step_none_legacy0 s _ h _ (immBytes 32 disp) (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    hcode hlow' hdecode ((hmode 6).of_cs_lma_eq rfl rfl)

end X86Proofs
