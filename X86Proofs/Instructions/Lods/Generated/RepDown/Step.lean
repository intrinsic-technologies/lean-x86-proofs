
import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.RepString
import X86Proofs.Instructions.Lods.Generated.Rep.Step

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def repLodsDownAfter (n len : Nat) (s : RamState) : RamState :=
  afterStep s len fun t =>
    repCount (lodsDownSpec n { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 len) })

theorem repLodsDownAfter_external (n len : Nat) (s : RamState) :
    (repLodsDownAfter n len s).external = s.external := rfl

@[simp] theorem repLodsDownAfter_rflags (n len : Nat) (s : RamState) :
    (repLodsDownAfter n len s).RFLAGS = s.RFLAGS := rfl

theorem repLodsDownAfter_gpr (n len : Nat) (s : RamState) :
    (repLodsDownAfter n len s).GPR =
      Vector.set (Vector.set (Vector.set s.GPR 0
        (mergeGPR n ((Operand.mem (rsi.read s) : Operand n).read s) s.GPR[0])) 6
        (s.GPR[6] - BitVec.ofNat _ (n / 8))) 1 (s.GPR[1] - 1) := by
  simp [repLodsDownAfter, repCount, afterStep, finishStep, lodsDownSpec, Operand.write, Operand.read,
    dataAccess, afterFetches, beforeFetch, resetStepFields, gprIndex, mergeGPR_64, Vector.getElem_set]
  rfl

theorem repLodsDownAfter_rsi (n len : Nat) (s : RamState) :
    rsi.read (repLodsDownAfter n len s) = rsi.read s - BitVec.ofNat 64 (n / 8) := by
  simp [Operand.read, repLodsDownAfter_gpr, gprIndex, Vector.getElem_set]
  rfl

theorem repLodsDownAfter_rcx (n len : Nat) (s : RamState) :
    rcx.read (repLodsDownAfter n len s) = rcx.read s - 1 := by
  simp [Operand.read, repLodsDownAfter_gpr, gprIndex]

theorem repLodsDownAfter_rax (n len : Nat) (s : RamState) :
    (Operand.reg 0 : Operand 64).read (repLodsDownAfter n len s) =
      mergeGPR n ((Operand.mem (rsi.read s) : Operand n).read s)
        ((Operand.reg 0 : Operand 64).read s) := by
  simp [Operand.read, repLodsDownAfter_gpr, gprIndex]

theorem rcx_read_lodsDownSpec (n : Nat) (t : RamState) :
    rcx.read (lodsDownSpec n t) = rcx.read t := by
  simp only [lodsDownSpec]
  rw [Operand.read_write_reg_of_ne _ (by decide), Operand.read_write_reg_of_ne _ (by decide),
    Operand.read_reg_dataAccess]

theorem repLodsDownAfter_repeat (n len : Nat) (s : RamState) :
    (repLodsDownAfter n len s).Repeat_String_Operation = !(rcx.read s - 1 == 0#64) := by
  simp only [repLodsDownAfter, afterStep, finishStep, repCount, rcx_read_lodsDownSpec]
  rfl

theorem repLodsDownAfter_rip (n len : Nat) (s : RamState) (hmsr : s.«MSRLIST::In_Process» = false) :
    (repLodsDownAfter n len s).RIP =
      if rcx.read s - 1 = 0 then BitVec.add s.RIP (BitVec.ofNat 64 len) else s.RIP := by
  simp only [repLodsDownAfter, afterStep, finishStep, repCount, rcx_read_lodsDownSpec]
  simp [lodsDownSpec, Operand.write, dataAccess, afterFetches, beforeFetch, resetStepFields, hmsr]

theorem AgreesExcept.repLodsDown (n len : Nat) (s : RamState) :
    AgreesExcept [.reg 0, .reg 1, .reg 6, .rip] (clearRep s)
      (clearRep (repLodsDownAfter n len s)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r =>
      have h0' : r ≠ 0 := fun h => hc (by simp [h])
      have h0 : r.toNat ≠ 0 := fun e => h0' (BitVec.eq_of_toNat_eq e)
      have h1' : r ≠ 1 := fun h => hc (by simp [h])
      have h1 : r.toNat ≠ 1 := fun e => h1' (BitVec.eq_of_toNat_eq e)
      have h6' : r ≠ 6 := fun h => hc (by simp [h])
      have h6 : r.toNat ≠ 6 := fun e => h6' (BitVec.eq_of_toNat_eq e)
      simp [Component.Agrees, clearRep, repLodsDownAfter_gpr, gprIndex, Ne.symm h0, Ne.symm h1, Ne.symm h6]
    | flags => rfl
    | rip => exact absurd (by simp) hc
    | mem a len => exact absurd hm (by simp [Component.isMem])
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => rfl
  · simp only [clearRep_external, repLodsDownAfter_external]
  · simp only [fixedPart, clearRep, repLodsDownAfter, repCount, afterStep, finishStep, lodsDownSpec,
      Operand.write, dataAccess, afterFetches, beforeFetch, resetStepFields]
  · simpa [clearRep_external, repLodsDownAfter_external] using hx

theorem ReadyMidRep.repLodsDown [Bindings] {s : RamState} (h : ReadyMidRep s) (n len : Nat) :
    ReadyMidRep (repLodsDownAfter n len s) := by
  have htab : IdentityPageTableMemory (clearRep (repLodsDownAfter n len s)).external := by
    rw [clearRep_external, repLodsDownAfter_external]
    exact (ReadyToStep.memory (s := clearRep s) h).tables
  have : ReadyToStep (clearRep (repLodsDownAfter n len s)) :=
    ReadyToStep.of_agreesExcept h.clear (AgreesExcept.repLodsDown n len s) htab
  exact this

theorem rep_lodsq_down_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAD]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rsi.read s) 8) :
    X86.Machine.step s = some (.next (repLodsDownAfter 64 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xAD]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAD]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_AD_rep_lodsq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_lodsq_down_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht haddr hrex2 hlock hw hseg hm64 hcpu.ds
    hdf hcount (hrd.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xAD : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAD [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_lodsd_down_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAD]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rsi.read s) 4) :
    X86.Machine.step s = some (.next (repLodsDownAfter 32 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xAD]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAD]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_AD_rep_lodsd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_lodsd_down_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht haddr hrex2 hlock hosz hw hseg hm64 hcpu.ds
    hdf hcount (hrd.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xAD : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAD [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_lodsw_down_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAD]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rsi.read s) 2) :
    X86.Machine.step s = some (.next (repLodsDownAfter 16 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xAD]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAD]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_AD_rep_lodsw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_lodsw_down_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht haddr hrex2 hlock hw hseg hm64 hcpu.ds
    hdf hcount (hrd.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xAD : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAD [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_lodsb_down_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAC]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rsi.read s) 1) :
    X86.Machine.step s = some (.next (repLodsDownAfter 8 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xAC]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAC]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_AC_rep_lodsb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_lodsb_down_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht haddr hrex2 hlock hseg hm64 hcpu.ds
    hdf hcount (hrd.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xAC : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAC [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

end X86Proofs
