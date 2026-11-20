
import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.RepString
import X86Proofs.Instructions.Scas.Generated.Repne.Step

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def repneScasDownAfter (n len : Nat) (s : RamState) : RamState :=
  afterStep s len fun t =>
    repneScasDownSpec n
      { t with
        Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 len), Repeat_String_Operation := true }

theorem repneScasDownSpec_cs (n : Nat) (t : RamState) : (repneScasDownSpec n t).CS = t.CS := by
  unfold repneScasDownSpec
  split <;> simp [Operand.write, scasDownSpec, setFlags, dataAccess]

theorem repneScasDownSpec_efer (n : Nat) (t : RamState) :
    (repneScasDownSpec n t).IA32_EFER = t.IA32_EFER := by
  unfold repneScasDownSpec
  split <;> simp [Operand.write, scasDownSpec, setFlags, dataAccess]

theorem repneScasDownSpec_zmm (n : Nat) (t : RamState) : (repneScasDownSpec n t).ZMM = t.ZMM := by
  unfold repneScasDownSpec
  split <;> simp [Operand.write, scasDownSpec, setFlags, dataAccess]

theorem repneScasDownSpec_mxcsr (n : Nat) (t : RamState) :
    (repneScasDownSpec n t).MXCSR = t.MXCSR := by
  unfold repneScasDownSpec
  split <;> simp [Operand.write, scasDownSpec, setFlags, dataAccess]

theorem repneScasDownSpec_fp87 (n : Nat) (t : RamState) : (repneScasDownSpec n t).FP87 = t.FP87 := by
  unfold repneScasDownSpec
  split <;> simp [Operand.write, scasDownSpec, setFlags, dataAccess]

theorem repneScasDownSpec_fsw (n : Nat) (t : RamState) :
    (repneScasDownSpec n t).FP87_Status = t.FP87_Status := by
  unfold repneScasDownSpec
  split <;> simp [Operand.write, scasDownSpec, setFlags, dataAccess]

theorem repneScasDownSpec_ftw (n : Nat) (t : RamState) :
    (repneScasDownSpec n t).FP87_Tag_Word = t.FP87_Tag_Word := by
  unfold repneScasDownSpec
  split <;> simp [Operand.write, scasDownSpec, setFlags, dataAccess]

theorem repneScasDownSpec_fcw (n : Nat) (t : RamState) :
    (repneScasDownSpec n t).FP87_Control = t.FP87_Control := by
  unfold repneScasDownSpec
  split <;> simp [Operand.write, scasDownSpec, setFlags, dataAccess]

theorem repneScasDownSpec_fpuPtr (n : Nat) (t : RamState) :
    fpuPtrOf (repneScasDownSpec n t) = fpuPtrOf t := by
  unfold repneScasDownSpec
  split <;> simp [Operand.write, scasDownSpec, setFlags, dataAccess, fpuPtrOf]

theorem repneScasDownSpec_external (n : Nat) (t : RamState) :
    (repneScasDownSpec n t).external = t.external := by
  unfold repneScasDownSpec
  split <;> simp [Operand.write, scasDownSpec, setFlags, dataAccess]

theorem repneScasDownSpec_repeat (n : Nat) (t : RamState) :
    (repneScasDownSpec n t).Repeat_String_Operation = repneScasCont n t := by
  unfold repneScasDownSpec
  split <;> simp_all

theorem repneScasDownSpec_rflags (n : Nat) (t : RamState) :
    (repneScasDownSpec n t).RFLAGS = if repneScasCont n t then t.RFLAGS else
      (cmpSpec ((Operand.reg 0 : Operand n).read t)
        ((Operand.mem (rdi.read t) : Operand n).read t)).store t.RFLAGS := by
  unfold repneScasDownSpec
  split <;> simp_all [Operand.write, scasDownSpec, setFlags, dataAccess]

theorem repneScasDownSpec_gpr (n : Nat) (t : RamState) :
    (repneScasDownSpec n t).GPR =
      Vector.set (Vector.set t.GPR 7 (t.GPR[7] - BitVec.ofNat _ (n / 8))) 1
        (t.GPR[1] - 1) := by
  unfold repneScasDownSpec
  split <;>
  · simp [scasDownSpec, Operand.write, Operand.read, setFlags, dataAccess, gprIndex, mergeGPR_64,
      Vector.getElem_set]
    rfl

theorem repneScasDownSpec_finish_rip (n : Nat) (t : RamState) (hb : t.Branch_Taken = false)
    (hm : t.«MSRLIST::In_Process» = false) :
    (finishStep (repneScasDownSpec n t)).RIP = if repneScasCont n t then t.RIP else t.Next_IP := by
  unfold finishStep repneScasDownSpec
  split <;> simp_all [Operand.write, scasDownSpec, setFlags, dataAccess]

theorem repneScasDownSpec_fixed (n : Nat) (t : RamState) :
    fixedPart (clearRep (repneScasDownSpec n t)) = fixedPart (clearRep t) := by
  unfold repneScasDownSpec
  split <;>
    simp only [fixedPart, clearRep, scasDownSpec, Operand.write, setFlags, dataAccess, beforeFetch,
      resetStepFields, clearStatusFlags_store]

theorem repneScasDownAfter_external (n len : Nat) (s : RamState) :
    (repneScasDownAfter n len s).external = s.external :=
  repneScasDownSpec_external n _

theorem repneScasDownAfter_gpr (n len : Nat) (s : RamState) :
    (repneScasDownAfter n len s).GPR =
      Vector.set (Vector.set s.GPR 7 (s.GPR[7] - BitVec.ofNat _ (n / 8))) 1
        (s.GPR[1] - 1) :=
  repneScasDownSpec_gpr n _

theorem repneScasDownAfter_rdi (n len : Nat) (s : RamState) :
    rdi.read (repneScasDownAfter n len s) = rdi.read s - BitVec.ofNat 64 (n / 8) := by
  simp [Operand.read, repneScasDownAfter_gpr, gprIndex, Vector.getElem_set]
  rfl

theorem repneScasDownAfter_rcx (n len : Nat) (s : RamState) :
    rcx.read (repneScasDownAfter n len s) = rcx.read s - 1 := by
  simp [Operand.read, repneScasDownAfter_gpr, gprIndex]

theorem repneScasDownAfter_acc (n len : Nat) (s : RamState) :
    (Operand.reg 0 : Operand n).read (repneScasDownAfter n len s) = (Operand.reg 0 : Operand n).read s := by
  simp [Operand.read, repneScasDownAfter_gpr, gprIndex]

theorem repneScasDownAfter_repeat (n len : Nat) (s : RamState) :
    (repneScasDownAfter n len s).Repeat_String_Operation = repneScasCont n s :=
  repneScasDownSpec_repeat n _

theorem repneScasDownAfter_rflags (n len : Nat) (s : RamState) :
    (repneScasDownAfter n len s).RFLAGS = if repneScasCont n s then s.RFLAGS else
      (cmpSpec ((Operand.reg 0 : Operand n).read s)
        ((Operand.mem (rdi.read s) : Operand n).read s)).store s.RFLAGS :=
  repneScasDownSpec_rflags n _

theorem repneScasDownAfter_rip (n len : Nat) (s : RamState) (hmsr : s.«MSRLIST::In_Process» = false) :
    (repneScasDownAfter n len s).RIP =
      if repneScasCont n s then s.RIP else BitVec.add s.RIP (BitVec.ofNat 64 len) :=
  repneScasDownSpec_finish_rip n _ rfl hmsr

theorem AgreesExcept.repneScasDown (n len : Nat) (s : RamState) :
    AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s)
      (clearRep (repneScasDownAfter n len s)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r =>
      have h1' : r ≠ 1 := fun h => hc (by simp [h])
      have h7' : r ≠ 7 := fun h => hc (by simp [h])
      have h1 : r.toNat ≠ 1 := fun e => h1' (BitVec.eq_of_toNat_eq e)
      have h7 : r.toNat ≠ 7 := fun e => h7' (BitVec.eq_of_toNat_eq e)
      simp [Component.Agrees, clearRep, repneScasDownAfter_gpr, gprIndex, Ne.symm h1, Ne.symm h7]
    | flags => exact absurd (by simp) hc
    | rip => exact absurd (by simp) hc
    | mem a len => exact absurd hm (by simp [Component.isMem])
    | xmm x =>
      exact Component.agrees_xmm_of_zmm (by
        rw [repneScasDownAfter, afterStep, clearRep_ZMM, finishStep_ZMM, repneScasDownSpec_zmm]
        rfl) x
    | mxcsr =>
      show _ = _
      rw [repneScasDownAfter, afterStep, clearRep_MXCSR, finishStep_MXCSR, repneScasDownSpec_mxcsr]
      rfl
    | fpr x =>
      show _ = _
      rw [repneScasDownAfter, afterStep, clearRep_FP87, finishStep_FP87, repneScasDownSpec_fp87]
      rfl
    | fsw =>
      show _ = _
      rw [repneScasDownAfter, afterStep, clearRep_FP87_Status, finishStep_FP87_Status,
        repneScasDownSpec_fsw]
      rfl
    | fcc =>
      show _ = _
      rw [repneScasDownAfter, afterStep, clearRep_FP87_Status, finishStep_FP87_Status,
        repneScasDownSpec_fsw]
      rfl
    | ftw =>
      show _ = _
      rw [repneScasDownAfter, afterStep, clearRep_FP87_Tag_Word, finishStep_FP87_Tag_Word,
        repneScasDownSpec_ftw]
      rfl
    | fcw =>
      show _ = _
      rw [repneScasDownAfter, afterStep, clearRep_FP87_Control, finishStep_FP87_Control,
        repneScasDownSpec_fcw]
      rfl
    | fpuPtr =>
      show _ = _
      rw [repneScasDownAfter, afterStep, fpuPtrOf_clearRep, fpuPtrOf_finishStep, repneScasDownSpec_fpuPtr]
      rfl
    | df =>
      show dfBit (repneScasDownAfter n len s).RFLAGS = dfBit s.RFLAGS
      rw [repneScasDownAfter_rflags]
      split <;> simp only [dfBit_store]
  · simp only [clearRep_external, repneScasDownAfter_external]
  · rw [repneScasDownAfter, afterStep, fixedPart_clearRep_finishStep, repneScasDownSpec_fixed]
    simp only [fixedPart, clearRep, afterFetches, beforeFetch, resetStepFields]
  · simpa [clearRep_external, repneScasDownAfter_external] using hx

theorem ReadyMidRep.repneScasDown [Bindings] {s : RamState} (h : ReadyMidRep s) (n len : Nat) :
    ReadyMidRep (repneScasDownAfter n len s) := by
  have htab : IdentityPageTableMemory (clearRep (repneScasDownAfter n len s)).external := by
    rw [clearRep_external, repneScasDownAfter_external]
    exact (ReadyToStep.memory (s := clearRep s) h).tables
  have : ReadyToStep (clearRep (repneScasDownAfter n len s)) :=
    ReadyToStep.of_agreesExcept h.clear (AgreesExcept.repneScasDown n len s) htab
  exact this

theorem repne_scasq_down_step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAF]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rdi.read s) 8) :
    X86.Machine.step s = some (.next (repneScasDownAfter 64 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xAF]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAF]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_AF_repne_scasq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repne_scasq_down_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hw
    hcpu.es hdf hcount (hrd.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xAF : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAF [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repneScasDownSpec_cs _ _)
      (by rw [repneScasDownSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repne_scasd_down_step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAF]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rdi.read s) 4) :
    X86.Machine.step s = some (.next (repneScasDownAfter 32 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xAF]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAF]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_AF_repne_scasd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repne_scasd_down_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hosz hw
    hcpu.es hdf hcount (hrd.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xAF : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAF [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repneScasDownSpec_cs _ _)
      (by rw [repneScasDownSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repne_scasw_down_step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAF]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rdi.read s) 2) :
    X86.Machine.step s = some (.next (repneScasDownAfter 16 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xAF]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAF]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_AF_repne_scasw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repne_scasw_down_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hw
    hcpu.es hdf hcount (hrd.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xAF : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAF [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repneScasDownSpec_cs _ _)
      (by rw [repneScasDownSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repne_scasb_down_step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAE]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rdi.read s) 1) :
    X86.Machine.step s = some (.next (repneScasDownAfter 8 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xAE]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAE]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_AE_repne_scasb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repne_scasb_down_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock
    hcpu.es hdf hcount (hrd.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xAE : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAE [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repneScasDownSpec_cs _ _)
      (by rw [repneScasDownSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

end X86Proofs
