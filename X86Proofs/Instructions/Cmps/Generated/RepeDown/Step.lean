
import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.RepString
import X86Proofs.Instructions.Cmps.Generated.Repe.Step

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def repeCmpsDownAfter (n len : Nat) (s : RamState) : RamState :=
  afterStep s len fun t =>
    repeCmpsDownSpec n
      { t with
        Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 len), Repeat_String_Operation := false }

theorem repeCmpsDownSpec_cs (n : Nat) (t : RamState) : (repeCmpsDownSpec n t).CS = t.CS := by
  unfold repeCmpsDownSpec
  split <;> simp [Operand.write, cmpsDownSpec, setFlags, dataAccess]

theorem repeCmpsDownSpec_efer (n : Nat) (t : RamState) :
    (repeCmpsDownSpec n t).IA32_EFER = t.IA32_EFER := by
  unfold repeCmpsDownSpec
  split <;> simp [Operand.write, cmpsDownSpec, setFlags, dataAccess]

theorem repeCmpsDownSpec_zmm (n : Nat) (t : RamState) : (repeCmpsDownSpec n t).ZMM = t.ZMM := by
  unfold repeCmpsDownSpec
  split <;> simp [Operand.write, cmpsDownSpec, setFlags, dataAccess]

theorem repeCmpsDownSpec_mxcsr (n : Nat) (t : RamState) :
    (repeCmpsDownSpec n t).MXCSR = t.MXCSR := by
  unfold repeCmpsDownSpec
  split <;> simp [Operand.write, cmpsDownSpec, setFlags, dataAccess]

theorem repeCmpsDownSpec_fp87 (n : Nat) (t : RamState) : (repeCmpsDownSpec n t).FP87 = t.FP87 := by
  unfold repeCmpsDownSpec
  split <;> simp [Operand.write, cmpsDownSpec, setFlags, dataAccess]

theorem repeCmpsDownSpec_fsw (n : Nat) (t : RamState) :
    (repeCmpsDownSpec n t).FP87_Status = t.FP87_Status := by
  unfold repeCmpsDownSpec
  split <;> simp [Operand.write, cmpsDownSpec, setFlags, dataAccess]

theorem repeCmpsDownSpec_ftw (n : Nat) (t : RamState) :
    (repeCmpsDownSpec n t).FP87_Tag_Word = t.FP87_Tag_Word := by
  unfold repeCmpsDownSpec
  split <;> simp [Operand.write, cmpsDownSpec, setFlags, dataAccess]

theorem repeCmpsDownSpec_fcw (n : Nat) (t : RamState) :
    (repeCmpsDownSpec n t).FP87_Control = t.FP87_Control := by
  unfold repeCmpsDownSpec
  split <;> simp [Operand.write, cmpsDownSpec, setFlags, dataAccess]

theorem repeCmpsDownSpec_fpuPtr (n : Nat) (t : RamState) :
    fpuPtrOf (repeCmpsDownSpec n t) = fpuPtrOf t := by
  unfold repeCmpsDownSpec
  split <;> simp [Operand.write, cmpsDownSpec, setFlags, dataAccess, fpuPtrOf]

theorem repeCmpsDownSpec_external (n : Nat) (t : RamState) :
    (repeCmpsDownSpec n t).external = t.external := by
  unfold repeCmpsDownSpec
  split <;> simp [Operand.write, cmpsDownSpec, setFlags, dataAccess]

theorem repeCmpsDownSpec_repeat (n : Nat) (t : RamState) :
    (repeCmpsDownSpec n t).Repeat_String_Operation = repeCmpsCont n t := by
  unfold repeCmpsDownSpec
  split <;> simp_all

theorem repeCmpsDownSpec_rflags (n : Nat) (t : RamState) :
    (repeCmpsDownSpec n t).RFLAGS = if repeCmpsCont n t then t.RFLAGS else
      (cmpSpec ((Operand.mem (rsi.read t) : Operand n).read t)
        ((Operand.mem (rdi.read t) : Operand n).read t)).store t.RFLAGS := by
  unfold repeCmpsDownSpec
  split <;> simp_all [Operand.write, cmpsDownSpec, setFlags, dataAccess]

theorem repeCmpsDownSpec_gpr (n : Nat) (t : RamState) :
    (repeCmpsDownSpec n t).GPR =
      Vector.set (Vector.set (Vector.set t.GPR 6 (t.GPR[6] - BitVec.ofNat _ (n / 8))) 7
        (t.GPR[7] - BitVec.ofNat _ (n / 8))) 1 (t.GPR[1] - 1) := by
  unfold repeCmpsDownSpec
  split <;>
  · simp [cmpsDownSpec, Operand.write, Operand.read, setFlags, dataAccess, gprIndex, mergeGPR_64,
      Vector.getElem_set]
    rfl

theorem repeCmpsDownSpec_finish_rip (n : Nat) (t : RamState) (hb : t.Branch_Taken = false)
    (hm : t.«MSRLIST::In_Process» = false) :
    (finishStep (repeCmpsDownSpec n t)).RIP = if repeCmpsCont n t then t.RIP else t.Next_IP := by
  unfold finishStep repeCmpsDownSpec
  split <;> simp_all [Operand.write, cmpsDownSpec, setFlags, dataAccess]

theorem repeCmpsDownSpec_fixed (n : Nat) (t : RamState) :
    fixedPart (clearRep (repeCmpsDownSpec n t)) = fixedPart (clearRep t) := by
  unfold repeCmpsDownSpec
  split <;>
    simp only [fixedPart, clearRep, cmpsDownSpec, Operand.write, setFlags, dataAccess, beforeFetch,
      resetStepFields, clearStatusFlags_store]

theorem repeCmpsDownAfter_external (n len : Nat) (s : RamState) :
    (repeCmpsDownAfter n len s).external = s.external :=
  repeCmpsDownSpec_external n _

theorem repeCmpsDownAfter_gpr (n len : Nat) (s : RamState) :
    (repeCmpsDownAfter n len s).GPR =
      Vector.set (Vector.set (Vector.set s.GPR 6 (s.GPR[6] - BitVec.ofNat _ (n / 8))) 7
        (s.GPR[7] - BitVec.ofNat _ (n / 8))) 1 (s.GPR[1] - 1) :=
  repeCmpsDownSpec_gpr n _

theorem repeCmpsDownAfter_rsi (n len : Nat) (s : RamState) :
    rsi.read (repeCmpsDownAfter n len s) = rsi.read s - BitVec.ofNat 64 (n / 8) := by
  simp [Operand.read, repeCmpsDownAfter_gpr, gprIndex, Vector.getElem_set]
  rfl

theorem repeCmpsDownAfter_rdi (n len : Nat) (s : RamState) :
    rdi.read (repeCmpsDownAfter n len s) = rdi.read s - BitVec.ofNat 64 (n / 8) := by
  simp [Operand.read, repeCmpsDownAfter_gpr, gprIndex, Vector.getElem_set]
  rfl

theorem repeCmpsDownAfter_rcx (n len : Nat) (s : RamState) :
    rcx.read (repeCmpsDownAfter n len s) = rcx.read s - 1 := by
  simp [Operand.read, repeCmpsDownAfter_gpr, gprIndex]

theorem repeCmpsDownAfter_repeat (n len : Nat) (s : RamState) :
    (repeCmpsDownAfter n len s).Repeat_String_Operation = repeCmpsCont n s :=
  repeCmpsDownSpec_repeat n _

theorem repeCmpsDownAfter_rflags (n len : Nat) (s : RamState) :
    (repeCmpsDownAfter n len s).RFLAGS = if repeCmpsCont n s then s.RFLAGS else
      (cmpSpec ((Operand.mem (rsi.read s) : Operand n).read s)
        ((Operand.mem (rdi.read s) : Operand n).read s)).store s.RFLAGS :=
  repeCmpsDownSpec_rflags n _

theorem repeCmpsDownAfter_rip (n len : Nat) (s : RamState) (hmsr : s.«MSRLIST::In_Process» = false) :
    (repeCmpsDownAfter n len s).RIP =
      if repeCmpsCont n s then s.RIP else BitVec.add s.RIP (BitVec.ofNat 64 len) :=
  repeCmpsDownSpec_finish_rip n _ rfl hmsr

theorem AgreesExcept.repeCmpsDown (n len : Nat) (s : RamState) :
    AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s)
      (clearRep (repeCmpsDownAfter n len s)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r =>
      have h1' : r ≠ 1 := fun h => hc (by simp [h])
      have h6' : r ≠ 6 := fun h => hc (by simp [h])
      have h7' : r ≠ 7 := fun h => hc (by simp [h])
      have h1 : r.toNat ≠ 1 := fun e => h1' (BitVec.eq_of_toNat_eq e)
      have h6 : r.toNat ≠ 6 := fun e => h6' (BitVec.eq_of_toNat_eq e)
      have h7 : r.toNat ≠ 7 := fun e => h7' (BitVec.eq_of_toNat_eq e)
      simp [Component.Agrees, clearRep, repeCmpsDownAfter_gpr, gprIndex, Ne.symm h1, Ne.symm h6, Ne.symm h7]
    | flags => exact absurd (by simp) hc
    | rip => exact absurd (by simp) hc
    | mem a len => exact absurd hm (by simp [Component.isMem])
    | xmm x =>
      exact Component.agrees_xmm_of_zmm (by
        rw [repeCmpsDownAfter, afterStep, clearRep_ZMM, finishStep_ZMM, repeCmpsDownSpec_zmm]
        rfl) x
    | mxcsr =>
      show _ = _
      rw [repeCmpsDownAfter, afterStep, clearRep_MXCSR, finishStep_MXCSR, repeCmpsDownSpec_mxcsr]
      rfl
    | fpr x =>
      show _ = _
      rw [repeCmpsDownAfter, afterStep, clearRep_FP87, finishStep_FP87, repeCmpsDownSpec_fp87]
      rfl
    | fsw =>
      show _ = _
      rw [repeCmpsDownAfter, afterStep, clearRep_FP87_Status, finishStep_FP87_Status,
        repeCmpsDownSpec_fsw]
      rfl
    | fcc =>
      show _ = _
      rw [repeCmpsDownAfter, afterStep, clearRep_FP87_Status, finishStep_FP87_Status,
        repeCmpsDownSpec_fsw]
      rfl
    | ftw =>
      show _ = _
      rw [repeCmpsDownAfter, afterStep, clearRep_FP87_Tag_Word, finishStep_FP87_Tag_Word,
        repeCmpsDownSpec_ftw]
      rfl
    | fcw =>
      show _ = _
      rw [repeCmpsDownAfter, afterStep, clearRep_FP87_Control, finishStep_FP87_Control,
        repeCmpsDownSpec_fcw]
      rfl
    | fpuPtr =>
      show _ = _
      rw [repeCmpsDownAfter, afterStep, fpuPtrOf_clearRep, fpuPtrOf_finishStep, repeCmpsDownSpec_fpuPtr]
      rfl
    | df =>
      show dfBit (repeCmpsDownAfter n len s).RFLAGS = dfBit s.RFLAGS
      rw [repeCmpsDownAfter_rflags]
      split <;> simp only [dfBit_store]
  · simp only [clearRep_external, repeCmpsDownAfter_external]
  · rw [repeCmpsDownAfter, afterStep, fixedPart_clearRep_finishStep, repeCmpsDownSpec_fixed]
    simp only [fixedPart, clearRep, afterFetches, beforeFetch, resetStepFields]
  · simpa [clearRep_external, repeCmpsDownAfter_external] using hx

theorem ReadyMidRep.repeCmpsDown [Bindings] {s : RamState} (h : ReadyMidRep s) (n len : Nat) :
    ReadyMidRep (repeCmpsDownAfter n len s) := by
  have htab : IdentityPageTableMemory (clearRep (repeCmpsDownAfter n len s)).external := by
    rw [clearRep_external, repeCmpsDownAfter_external]
    exact (ReadyToStep.memory (s := clearRep s) h).tables
  have : ReadyToStep (clearRep (repeCmpsDownAfter n len s)) :=
    ReadyToStep.of_agreesExcept h.clear (AgreesExcept.repeCmpsDown n len s) htab
  exact this

theorem repe_cmpsq_down_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (rsi.read s) 8) (hdst : MemReadable s (rdi.read s) 8) :
    X86.Machine.step s = some (.next (repeCmpsDownAfter 64 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repe_cmpsq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repe_cmpsq_down_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hcpu.ds hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repeCmpsDownSpec_cs _ _)
      (by rw [repeCmpsDownSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repe_cmpsd_down_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (rsi.read s) 4) (hdst : MemReadable s (rdi.read s) 4) :
    X86.Machine.step s = some (.next (repeCmpsDownAfter 32 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repe_cmpsd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repe_cmpsd_down_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hcpu.ds hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repeCmpsDownSpec_cs _ _)
      (by rw [repeCmpsDownSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repe_cmpsw_down_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (rsi.read s) 2) (hdst : MemReadable s (rdi.read s) 2) :
    X86.Machine.step s = some (.next (repeCmpsDownAfter 16 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repe_cmpsw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repe_cmpsw_down_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hcpu.ds hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repeCmpsDownSpec_cs _ _)
      (by rw [repeCmpsDownSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repe_cmpsb_down_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA6]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (rsi.read s) 1) (hdst : MemReadable s (rdi.read s) 1) :
    X86.Machine.step s = some (.next (repeCmpsDownAfter 8 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA6]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA6]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A6_repe_cmpsb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repe_cmpsb_down_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hcpu.ds hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA6 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA6 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repeCmpsDownSpec_cs _ _)
      (by rw [repeCmpsDownSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

end X86Proofs
