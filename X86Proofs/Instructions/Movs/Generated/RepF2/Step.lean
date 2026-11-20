
import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.RepString
import X86Proofs.Instructions.Movs.RepStep
import X86Proofs.Instructions.Movs.Generated.RepF2.Decode
import X86Proofs.Instructions.Movs.Generated.RepF2.Form
import X86Proofs.Instructions.Movs.Generated.Rep.Step

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem rep_movsq_f2_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rsi.read s) 8) (hwr : MemWritable s (rdi.read s) 8) :
    X86.Machine.step s = some (.next (repMovsAfter 64 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsq_f2 s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsq_f2_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hw hseg hm64 hcpu.ds hcpu.es
    hdf hcount (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsq_f2_seg_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 8) (hwr : MemWritable s (rdi.read s) 8) :
    X86.Machine.step s = some (.next (repMovsSegAfter (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 64
      (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsq_f2 s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsq_f2_seg_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hw hseg hsr hcpu.es
    hdf hcount (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsq_f2_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsq_f2 s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [rep_movsq_f2_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ haddr hrex2 hlock hw hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsd_f2_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rsi.read s) 4) (hwr : MemWritable s (rdi.read s) 4) :
    X86.Machine.step s = some (.next (repMovsAfter 32 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsd_f2 s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsd_f2_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hosz hw hseg hm64 hcpu.ds hcpu.es
    hdf hcount (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsd_f2_seg_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 4) (hwr : MemWritable s (rdi.read s) 4) :
    X86.Machine.step s = some (.next (repMovsSegAfter (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 32
      (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsd_f2 s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsd_f2_seg_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hosz hw hseg hsr hcpu.es
    hdf hcount (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsd_f2_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsd_f2 s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [rep_movsd_f2_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ haddr hrex2 hlock hosz hw hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsw_f2_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rsi.read s) 2) (hwr : MemWritable s (rdi.read s) 2) :
    X86.Machine.step s = some (.next (repMovsAfter 16 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsw_f2 s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsw_f2_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hw hseg hm64 hcpu.ds hcpu.es
    hdf hcount (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsw_f2_seg_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 2) (hwr : MemWritable s (rdi.read s) 2) :
    X86.Machine.step s = some (.next (repMovsSegAfter (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 16
      (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsw_f2 s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsw_f2_seg_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hw hseg hsr hcpu.es
    hdf hcount (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsw_f2_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsw_f2 s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [rep_movsw_f2_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ haddr hrex2 hlock hw hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsb_f2_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA4]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rsi.read s) 1) (hwr : MemWritable s (rdi.read s) 1) :
    X86.Machine.step s = some (.next (repMovsAfter 8 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA4]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA4]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A4_rep_movsb_f2 s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsb_f2_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hseg hm64 hcpu.ds hcpu.es
    hdf hcount (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA4 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA4 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsb_f2_seg_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA4]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 1) (hwr : MemWritable s (rdi.read s) 1) :
    X86.Machine.step s = some (.next (repMovsSegAfter (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 8
      (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA4]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA4]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A4_rep_movsb_f2 s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsb_f2_seg_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hseg hsr hcpu.es
    hdf hcount (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA4 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA4 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsb_f2_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xA4]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA4]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA4]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A4_rep_movsb_f2 s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [rep_movsb_f2_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ haddr hrex2 hlock hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA4 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA4 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

end X86Proofs
