
import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.RepString
import X86Proofs.Instructions.Scas.Generated.Repne.Decode
import X86Proofs.Instructions.Scas.Generated.Repne.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def repneScasAfter (n len : Nat) (s : RamState) : RamState :=
  afterStep s len fun t =>
    repneScasSpec n
      { t with
        Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 len), Repeat_String_Operation := true }

theorem repneScasSpec_cs (n : Nat) (t : RamState) : (repneScasSpec n t).CS = t.CS := by
  unfold repneScasSpec
  split <;> simp [Operand.write, scasSpec, setFlags, dataAccess]

theorem repneScasSpec_efer (n : Nat) (t : RamState) :
    (repneScasSpec n t).IA32_EFER = t.IA32_EFER := by
  unfold repneScasSpec
  split <;> simp [Operand.write, scasSpec, setFlags, dataAccess]

theorem repneScasSpec_zmm (n : Nat) (t : RamState) : (repneScasSpec n t).ZMM = t.ZMM := by
  unfold repneScasSpec
  split <;> simp [Operand.write, scasSpec, setFlags, dataAccess]

theorem repneScasSpec_mxcsr (n : Nat) (t : RamState) :
    (repneScasSpec n t).MXCSR = t.MXCSR := by
  unfold repneScasSpec
  split <;> simp [Operand.write, scasSpec, setFlags, dataAccess]

theorem repneScasSpec_fp87 (n : Nat) (t : RamState) : (repneScasSpec n t).FP87 = t.FP87 := by
  unfold repneScasSpec
  split <;> simp [Operand.write, scasSpec, setFlags, dataAccess]

theorem repneScasSpec_fsw (n : Nat) (t : RamState) :
    (repneScasSpec n t).FP87_Status = t.FP87_Status := by
  unfold repneScasSpec
  split <;> simp [Operand.write, scasSpec, setFlags, dataAccess]

theorem repneScasSpec_ftw (n : Nat) (t : RamState) :
    (repneScasSpec n t).FP87_Tag_Word = t.FP87_Tag_Word := by
  unfold repneScasSpec
  split <;> simp [Operand.write, scasSpec, setFlags, dataAccess]

theorem repneScasSpec_fcw (n : Nat) (t : RamState) :
    (repneScasSpec n t).FP87_Control = t.FP87_Control := by
  unfold repneScasSpec
  split <;> simp [Operand.write, scasSpec, setFlags, dataAccess]

theorem repneScasSpec_fpuPtr (n : Nat) (t : RamState) :
    fpuPtrOf (repneScasSpec n t) = fpuPtrOf t := by
  unfold repneScasSpec
  split <;> simp [Operand.write, scasSpec, setFlags, dataAccess, fpuPtrOf]

theorem repneScasSpec_external (n : Nat) (t : RamState) :
    (repneScasSpec n t).external = t.external := by
  unfold repneScasSpec
  split <;> simp [Operand.write, scasSpec, setFlags, dataAccess]

theorem repneScasSpec_repeat (n : Nat) (t : RamState) :
    (repneScasSpec n t).Repeat_String_Operation = repneScasCont n t := by
  unfold repneScasSpec
  split <;> simp_all

theorem repneScasSpec_rflags (n : Nat) (t : RamState) :
    (repneScasSpec n t).RFLAGS = if repneScasCont n t then t.RFLAGS else
      (cmpSpec ((Operand.reg 0 : Operand n).read t)
        ((Operand.mem (rdi.read t) : Operand n).read t)).store t.RFLAGS := by
  unfold repneScasSpec
  split <;> simp_all [Operand.write, scasSpec, setFlags, dataAccess]

theorem repneScasSpec_gpr (n : Nat) (t : RamState) :
    (repneScasSpec n t).GPR =
      Vector.set (Vector.set t.GPR 7 (t.GPR[7] + BitVec.ofNat _ (n / 8))) 1
        (t.GPR[1] - 1) := by
  unfold repneScasSpec
  split <;>
  · simp [scasSpec, Operand.write, Operand.read, setFlags, dataAccess, gprIndex, mergeGPR_64,
      Vector.getElem_set]
    rfl

theorem repneScasSpec_finish_rip (n : Nat) (t : RamState) (hb : t.Branch_Taken = false)
    (hm : t.«MSRLIST::In_Process» = false) :
    (finishStep (repneScasSpec n t)).RIP = if repneScasCont n t then t.RIP else t.Next_IP := by
  unfold finishStep repneScasSpec
  split <;> simp_all [Operand.write, scasSpec, setFlags, dataAccess]

theorem repneScasSpec_fixed (n : Nat) (t : RamState) :
    fixedPart (clearRep (repneScasSpec n t)) = fixedPart (clearRep t) := by
  unfold repneScasSpec
  split <;>
    simp only [fixedPart, clearRep, scasSpec, Operand.write, setFlags, dataAccess, beforeFetch,
      resetStepFields, clearStatusFlags_store]

theorem repneScasAfter_external (n len : Nat) (s : RamState) :
    (repneScasAfter n len s).external = s.external :=
  repneScasSpec_external n _

theorem repneScasAfter_gpr (n len : Nat) (s : RamState) :
    (repneScasAfter n len s).GPR =
      Vector.set (Vector.set s.GPR 7 (s.GPR[7] + BitVec.ofNat _ (n / 8))) 1
        (s.GPR[1] - 1) :=
  repneScasSpec_gpr n _

theorem repneScasAfter_rdi (n len : Nat) (s : RamState) :
    rdi.read (repneScasAfter n len s) = rdi.read s + BitVec.ofNat 64 (n / 8) := by
  simp [Operand.read, repneScasAfter_gpr, gprIndex, Vector.getElem_set]
  rfl

theorem repneScasAfter_rcx (n len : Nat) (s : RamState) :
    rcx.read (repneScasAfter n len s) = rcx.read s - 1 := by
  simp [Operand.read, repneScasAfter_gpr, gprIndex]

theorem repneScasAfter_acc (n len : Nat) (s : RamState) :
    (Operand.reg 0 : Operand n).read (repneScasAfter n len s) = (Operand.reg 0 : Operand n).read s := by
  simp [Operand.read, repneScasAfter_gpr, gprIndex]

theorem repneScasAfter_repeat (n len : Nat) (s : RamState) :
    (repneScasAfter n len s).Repeat_String_Operation = repneScasCont n s :=
  repneScasSpec_repeat n _

theorem repneScasAfter_rflags (n len : Nat) (s : RamState) :
    (repneScasAfter n len s).RFLAGS = if repneScasCont n s then s.RFLAGS else
      (cmpSpec ((Operand.reg 0 : Operand n).read s)
        ((Operand.mem (rdi.read s) : Operand n).read s)).store s.RFLAGS :=
  repneScasSpec_rflags n _

theorem repneScasAfter_rip (n len : Nat) (s : RamState) (hmsr : s.«MSRLIST::In_Process» = false) :
    (repneScasAfter n len s).RIP =
      if repneScasCont n s then s.RIP else BitVec.add s.RIP (BitVec.ofNat 64 len) :=
  repneScasSpec_finish_rip n _ rfl hmsr

theorem AgreesExcept.repneScas (n len : Nat) (s : RamState) :
    AgreesExcept [.reg 1, .reg 7, .flags, .rip] (clearRep s)
      (clearRep (repneScasAfter n len s)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r =>
      have h1' : r ≠ 1 := fun h => hc (by simp [h])
      have h7' : r ≠ 7 := fun h => hc (by simp [h])
      have h1 : r.toNat ≠ 1 := fun e => h1' (BitVec.eq_of_toNat_eq e)
      have h7 : r.toNat ≠ 7 := fun e => h7' (BitVec.eq_of_toNat_eq e)
      simp [Component.Agrees, clearRep, repneScasAfter_gpr, gprIndex, Ne.symm h1, Ne.symm h7]
    | flags => exact absurd (by simp) hc
    | rip => exact absurd (by simp) hc
    | mem a len => exact absurd hm (by simp [Component.isMem])
    | xmm x =>
      exact Component.agrees_xmm_of_zmm (by
        rw [repneScasAfter, afterStep, clearRep_ZMM, finishStep_ZMM, repneScasSpec_zmm]
        rfl) x
    | mxcsr =>
      show _ = _
      rw [repneScasAfter, afterStep, clearRep_MXCSR, finishStep_MXCSR, repneScasSpec_mxcsr]
      rfl
    | fpr x =>
      show _ = _
      rw [repneScasAfter, afterStep, clearRep_FP87, finishStep_FP87, repneScasSpec_fp87]
      rfl
    | fsw =>
      show _ = _
      rw [repneScasAfter, afterStep, clearRep_FP87_Status, finishStep_FP87_Status,
        repneScasSpec_fsw]
      rfl
    | fcc =>
      show _ = _
      rw [repneScasAfter, afterStep, clearRep_FP87_Status, finishStep_FP87_Status,
        repneScasSpec_fsw]
      rfl
    | ftw =>
      show _ = _
      rw [repneScasAfter, afterStep, clearRep_FP87_Tag_Word, finishStep_FP87_Tag_Word,
        repneScasSpec_ftw]
      rfl
    | fcw =>
      show _ = _
      rw [repneScasAfter, afterStep, clearRep_FP87_Control, finishStep_FP87_Control,
        repneScasSpec_fcw]
      rfl
    | fpuPtr =>
      show _ = _
      rw [repneScasAfter, afterStep, fpuPtrOf_clearRep, fpuPtrOf_finishStep, repneScasSpec_fpuPtr]
      rfl
    | df =>
      show dfBit (repneScasAfter n len s).RFLAGS = dfBit s.RFLAGS
      rw [repneScasAfter_rflags]
      split <;> simp only [dfBit_store]
  · simp only [clearRep_external, repneScasAfter_external]
  · rw [repneScasAfter, afterStep, fixedPart_clearRep_finishStep, repneScasSpec_fixed]
    simp only [fixedPart, clearRep, afterFetches, beforeFetch, resetStepFields]
  · simpa [clearRep_external, repneScasAfter_external] using hx

theorem ReadyMidRep.repneScas [Bindings] {s : RamState} (h : ReadyMidRep s) (n len : Nat) :
    ReadyMidRep (repneScasAfter n len s) := by
  have htab : IdentityPageTableMemory (clearRep (repneScasAfter n len s)).external := by
    rw [clearRep_external, repneScasAfter_external]
    exact (ReadyToStep.memory (s := clearRep s) h).tables
  have : ReadyToStep (clearRep (repneScasAfter n len s)) :=
    ReadyToStep.of_agreesExcept h.clear (AgreesExcept.repneScas n len s) htab
  exact this

theorem repne_scasq_step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAF]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rdi.read s) 8) :
    X86.Machine.step s = some (.next (repneScasAfter 64 (pre.length + 1) s)) := by
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
  rw [repne_scasq_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hw
    hcpu.es hdf hcount (hrd.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xAF : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAF [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repneScasSpec_cs _ _)
      (by rw [repneScasSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repne_scasq_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xAF]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xAF]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAF]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_AF_repne_scasq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [repne_scasq_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ haddr hrex2 hlock hw
    hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xAF : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAF [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem repne_scasd_step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAF]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rdi.read s) 4) :
    X86.Machine.step s = some (.next (repneScasAfter 32 (pre.length + 1) s)) := by
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
  rw [repne_scasd_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hosz hw
    hcpu.es hdf hcount (hrd.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xAF : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAF [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repneScasSpec_cs _ _)
      (by rw [repneScasSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repne_scasd_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xAF]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xAF]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAF]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_AF_repne_scasd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [repne_scasd_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ haddr hrex2 hlock hosz hw
    hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xAF : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAF [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem repne_scasw_step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAF]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rdi.read s) 2) :
    X86.Machine.step s = some (.next (repneScasAfter 16 (pre.length + 1) s)) := by
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
  rw [repne_scasw_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hw
    hcpu.es hdf hcount (hrd.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xAF : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAF [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repneScasSpec_cs _ _)
      (by rw [repneScasSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repne_scasw_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xAF]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xAF]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAF]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_AF_repne_scasw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [repne_scasw_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ haddr hrex2 hlock hw
    hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xAF : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAF [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem repne_scasb_step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAE]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rdi.read s) 1) :
    X86.Machine.step s = some (.next (repneScasAfter 8 (pre.length + 1) s)) := by
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
  rw [repne_scasb_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock
    hcpu.es hdf hcount (hrd.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xAE : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAE [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repneScasSpec_cs _ _)
      (by rw [repneScasSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repne_scasb_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xAE]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xAE]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAE]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_AE_repne_scasb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [repne_scasb_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ haddr hrex2 hlock
    hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xAE : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAE [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem repne_scasq_a32_step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAF]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rdi.read s) 8)
    (hdl : (rdi.read s).toNat + 8 < 2^32) (hcl : (rcx.read s).toNat < 2^32) :
    X86.Machine.step s = some (.next (repneScasAfter 64 (pre.length + 1) s)) := by
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
  rw [repne_scasq_a32_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hw
    hcpu.es hdf hcount (hrd.of_external_eq rfl) hdl hcl] at hdecode
  have hpreserve : scanPreservesRepeat (0xAF : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAF [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repneScasSpec_cs _ _)
      (by rw [repneScasSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repne_scasq_a32_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xAF]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xAF]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAF]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_AF_repne_scasq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [repne_scasq_a32_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ haddr hrex2 hlock hw
    hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xAF : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAF [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem repne_scasd_a32_step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAF]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rdi.read s) 4)
    (hdl : (rdi.read s).toNat + 4 < 2^32) (hcl : (rcx.read s).toNat < 2^32) :
    X86.Machine.step s = some (.next (repneScasAfter 32 (pre.length + 1) s)) := by
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
  rw [repne_scasd_a32_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hosz hw
    hcpu.es hdf hcount (hrd.of_external_eq rfl) hdl hcl] at hdecode
  have hpreserve : scanPreservesRepeat (0xAF : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAF [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repneScasSpec_cs _ _)
      (by rw [repneScasSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repne_scasd_a32_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xAF]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xAF]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAF]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_AF_repne_scasd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [repne_scasd_a32_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ haddr hrex2 hlock hosz hw
    hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xAF : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAF [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem repne_scasw_a32_step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAF]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rdi.read s) 2)
    (hdl : (rdi.read s).toNat + 2 < 2^32) (hcl : (rcx.read s).toNat < 2^32) :
    X86.Machine.step s = some (.next (repneScasAfter 16 (pre.length + 1) s)) := by
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
  rw [repne_scasw_a32_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hw
    hcpu.es hdf hcount (hrd.of_external_eq rfl) hdl hcl] at hdecode
  have hpreserve : scanPreservesRepeat (0xAF : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAF [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repneScasSpec_cs _ _)
      (by rw [repneScasSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repne_scasw_a32_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xAF]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xAF]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAF]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_AF_repne_scasw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [repne_scasw_a32_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ haddr hrex2 hlock hw
    hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xAF : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAF [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem repne_scasb_a32_step [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAE]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rdi.read s) 1)
    (hdl : (rdi.read s).toNat + 1 < 2^32) (hcl : (rcx.read s).toNat < 2^32) :
    X86.Machine.step s = some (.next (repneScasAfter 8 (pre.length + 1) s)) := by
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
  rw [repne_scasb_a32_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock
    hcpu.es hdf hcount (hrd.of_external_eq rfl) hdl hcl] at hdecode
  have hpreserve : scanPreservesRepeat (0xAE : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAE [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repneScasSpec_cs _ _)
      (by rw [repneScasSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repne_scasb_a32_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xAE]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xAE]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAE]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_AE_repne_scasb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [repne_scasb_a32_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ haddr hrex2 hlock
    hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xAE : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAE [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

end X86Proofs
