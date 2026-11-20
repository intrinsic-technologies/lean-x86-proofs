
import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.RepString
import X86Proofs.Instructions.Stos.Generated.RepF2.Decode
import X86Proofs.Instructions.Stos.Generated.RepF2.Form
import X86Proofs.Instructions.Stos.Generated.Rep.Step

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem rep_stosq_f2_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAB]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hwr : MemWritable s (rdi.read s) 8) :
    X86.Machine.step s = some (.next (repStosAfter 64 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xAB]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAB]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_AB_rep_stosq_f2 s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_stosq_f2_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hw hcpu.es
    hdf hcount (hwr.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xAB : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAB [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_stosq_f2_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xAB]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xAB]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAB]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_AB_rep_stosq_f2 s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [rep_stosq_f2_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ haddr hrex2 hlock hw hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xAB : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAB [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_stosd_f2_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAB]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hwr : MemWritable s (rdi.read s) 4) :
    X86.Machine.step s = some (.next (repStosAfter 32 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xAB]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAB]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_AB_rep_stosd_f2 s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_stosd_f2_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hosz hw hcpu.es
    hdf hcount (hwr.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xAB : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAB [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_stosd_f2_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xAB]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xAB]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAB]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_AB_rep_stosd_f2 s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [rep_stosd_f2_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ haddr hrex2 hlock hosz hw hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xAB : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAB [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_stosw_f2_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAB]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hwr : MemWritable s (rdi.read s) 2) :
    X86.Machine.step s = some (.next (repStosAfter 16 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xAB]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAB]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_AB_rep_stosw_f2 s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_stosw_f2_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hw hcpu.es
    hdf hcount (hwr.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xAB : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAB [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_stosw_f2_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xAB]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xAB]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAB]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_AB_rep_stosw_f2 s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [rep_stosw_f2_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ haddr hrex2 hlock hw hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xAB : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAB [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_stosb_f2_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAA]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hwr : MemWritable s (rdi.read s) 1) :
    X86.Machine.step s = some (.next (repStosAfter 8 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xAA]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAA]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_AA_rep_stosb_f2 s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_stosb_f2_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hcpu.es
    hdf hcount (hwr.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xAA : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAA [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_stosb_f2_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xAA]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xAA]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAA]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_AA_rep_stosb_f2 s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [rep_stosb_f2_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ haddr hrex2 hlock hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xAA : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xAA [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

end X86Proofs
