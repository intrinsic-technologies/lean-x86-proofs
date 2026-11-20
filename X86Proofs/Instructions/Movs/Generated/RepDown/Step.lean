
import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.RepString
import X86Proofs.Instructions.Movs.RepStep
import X86Proofs.Instructions.Movs.Generated.Rep.Step

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def repMovsDownAfter (n len : Nat) (s : RamState) : RamState :=
  afterStep s len fun t =>
    repCount (movsDownSpec n { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 len) })

theorem repMovsDownAfter_external (n len : Nat) (s : RamState) :
    (repMovsDownAfter n len s).external =
      memStore s.external (rdi.read s) ((Operand.mem (rsi.read s) : Operand n).read s) := rfl

@[simp] theorem repMovsDownAfter_rflags (n len : Nat) (s : RamState) :
    (repMovsDownAfter n len s).RFLAGS = s.RFLAGS := rfl

theorem repMovsDownAfter_gpr (n len : Nat) (s : RamState) :
    (repMovsDownAfter n len s).GPR =
      Vector.set (Vector.set (Vector.set s.GPR 6 (s.GPR[6] - BitVec.ofNat _ (n / 8))) 7
        (s.GPR[7] - BitVec.ofNat _ (n / 8))) 1 (s.GPR[1] - 1) := by
  simp [repMovsDownAfter, repCount, afterStep, finishStep, movsDownSpec, Operand.write, Operand.read,
    dataAccess, afterFetches, beforeFetch, resetStepFields, gprIndex, mergeGPR_64, Vector.getElem_set]
  rfl

theorem repMovsDownAfter_rsi (n len : Nat) (s : RamState) :
    rsi.read (repMovsDownAfter n len s) = rsi.read s - BitVec.ofNat 64 (n / 8) := by
  simp [Operand.read, repMovsDownAfter_gpr, gprIndex, Vector.getElem_set]
  rfl

theorem repMovsDownAfter_rdi (n len : Nat) (s : RamState) :
    rdi.read (repMovsDownAfter n len s) = rdi.read s - BitVec.ofNat 64 (n / 8) := by
  simp [Operand.read, repMovsDownAfter_gpr, gprIndex, Vector.getElem_set]
  rfl

theorem repMovsDownAfter_rcx (n len : Nat) (s : RamState) :
    rcx.read (repMovsDownAfter n len s) = rcx.read s - 1 := by
  simp [Operand.read, repMovsDownAfter_gpr, gprIndex]

theorem rcx_read_movsDownSpec (n : Nat) (t : RamState) :
    rcx.read (movsDownSpec n t) = rcx.read t := by
  simp only [movsDownSpec]
  rw [Operand.read_write_reg_of_ne _ (by decide), Operand.read_write_reg_of_ne _ (by decide),
    Operand.read_reg_write_mem, Operand.read_reg_dataAccess, Operand.read_reg_dataAccess]

theorem repMovsDownAfter_repeat (n len : Nat) (s : RamState) :
    (repMovsDownAfter n len s).Repeat_String_Operation = !(rcx.read s - 1 == 0#64) := by
  simp only [repMovsDownAfter, afterStep, finishStep, repCount, rcx_read_movsDownSpec]
  rfl

theorem repMovsDownAfter_rip (n len : Nat) (s : RamState) (hmsr : s.«MSRLIST::In_Process» = false) :
    (repMovsDownAfter n len s).RIP =
      if rcx.read s - 1 = 0 then BitVec.add s.RIP (BitVec.ofNat 64 len) else s.RIP := by
  simp only [repMovsDownAfter, afterStep, finishStep, repCount, rcx_read_movsDownSpec]
  simp [movsDownSpec, Operand.write, dataAccess, afterFetches, beforeFetch, resetStepFields, hmsr]

theorem AgreesExcept.repMovsDown (n len : Nat) (s : RamState) :
    AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read s) (n / 8), .rip] (clearRep s)
      (clearRep (repMovsDownAfter n len s)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r =>
      have h1' : r ≠ 1 := fun h => hc (by simp [h])
      have h1 : r.toNat ≠ 1 := fun e => h1' (BitVec.eq_of_toNat_eq e)
      have h6' : r ≠ 6 := fun h => hc (by simp [h])
      have h6 : r.toNat ≠ 6 := fun e => h6' (BitVec.eq_of_toNat_eq e)
      have h7' : r ≠ 7 := fun h => hc (by simp [h])
      have h7 : r.toNat ≠ 7 := fun e => h7' (BitVec.eq_of_toNat_eq e)
      simp [Component.Agrees, clearRep, repMovsDownAfter_gpr, gprIndex, Ne.symm h1, Ne.symm h6, Ne.symm h7]
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
  · simp only [clearRep_external]
    rw [repMovsDownAfter_external]
    apply memStore_getElem?_of_ne
    intro i hi he
    exact hx (.mem (rdi.read s) (n / 8)) (by simp) ⟨i, hi, he.symm⟩
  · simp only [fixedPart, clearRep, repMovsDownAfter, repCount, afterStep, finishStep, movsDownSpec,
      Operand.write, dataAccess, afterFetches, beforeFetch, resetStepFields]
  · simp only [clearRep_external] at hx ⊢
    rw [repMovsDownAfter_external]
    exact memStore_isSome _ _ _ x hx

theorem ReadyMidRep.repMovsDown [Bindings] {s : RamState} (h : ReadyMidRep s) (n len : Nat)
    (hdst : (rdi.read s).toNat + n / 8 ≤ 2^32)
    (htables : PageTableEntriesApart (rdi.read s).toNat (n / 8)) :
    ReadyMidRep (repMovsDownAfter n len s) := by
  have htab : IdentityPageTableMemory (clearRep (repMovsDownAfter n len s)).external := by
    rw [clearRep_external, repMovsDownAfter_external]
    exact IdentityPageTableMemory.memStore (ReadyToStep.memory (s := clearRep s) h).tables _ _
      hdst htables
  have : ReadyToStep (clearRep (repMovsDownAfter n len s)) :=
    ReadyToStep.of_agreesExcept h.clear (AgreesExcept.repMovsDown n len s) htab
  exact this

theorem repMovsDownAfter_copy (n len : Nat) (s : RamState) (hn : n ≤ 128) (i : Nat) (hi : i < n / 8)
    (hsrc : (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome) :
    (repMovsDownAfter n len s).external[rdi.read s + BitVec.ofNat 64 i]? =
      s.external[rsi.read s + BitVec.ofNat 64 i]? := by
  rw [repMovsDownAfter_external, memStore_getElem?_self _ _ _ hn i hi]
  simp only [Operand.read]
  rw [storedByte_memLoad _ _ i hi, memByte]
  simp only [PhysicalMemory.read]
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsrc
  change some ((s.external[rsi.read s + BitVec.ofNat 64 i]?).getD 0) =
    s.external[rsi.read s + BitVec.ofNat 64 i]?
  rw [hb]
  rfl

theorem rep_movsq_down_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rsi.read s) 8) (hwr : MemWritable s (rdi.read s) 8) :
    X86.Machine.step s = some (.next (repMovsDownAfter 64 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsq_down_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hw hseg hm64 hcpu.ds hcpu.es
    hdf hcount (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsd_down_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
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
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rsi.read s) 4) (hwr : MemWritable s (rdi.read s) 4) :
    X86.Machine.step s = some (.next (repMovsDownAfter 32 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsd_down_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hosz hw hseg hm64 hcpu.ds hcpu.es
    hdf hcount (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsw_down_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
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
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rsi.read s) 2) (hwr : MemWritable s (rdi.read s) 2) :
    X86.Machine.step s = some (.next (repMovsDownAfter 16 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsw_down_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hw hseg hm64 hcpu.ds hcpu.es
    hdf hcount (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsb_down_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA4]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rsi.read s) 1) (hwr : MemWritable s (rdi.read s) 1) :
    X86.Machine.step s = some (.next (repMovsDownAfter 8 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA4]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA4]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A4_rep_movsb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsb_down_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hseg hm64 hcpu.ds hcpu.es
    hdf hcount (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA4 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA4 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

end X86Proofs
