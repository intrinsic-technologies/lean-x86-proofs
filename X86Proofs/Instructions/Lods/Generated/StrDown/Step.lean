
import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.String
import X86Proofs.Instructions.Lods.Generated.Str.Decode
import X86Proofs.Instructions.Lods.Generated.Str.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem afterStep_lods_down_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length n : Nat)
    (ip : BitVec 64) :
    (afterStep s length fun t => lodsDownSpec n { t with Next_IP := ip }).RIP = ip := by
  simp [afterStep, finishStep, lodsDownSpec, Operand.write, dataAccess, afterFetches,
    beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

@[simp] theorem afterStep_lods_down_external (s : RamState) (length n : Nat) (ip : BitVec 64) :
    (afterStep s length fun t => lodsDownSpec n { t with Next_IP := ip }).external = s.external := rfl

theorem Operand.read_afterStep_lods_down_rsi (s : RamState) (length n : Nat) (ip : BitVec 64) :
    rsi.read (afterStep s length fun t => lodsDownSpec n { t with Next_IP := ip }) = rsi.read s - BitVec.ofNat 64 (n / 8) := by
  rw [Operand.read_afterStep]
  simp [lodsDownSpec, afterFetches, beforeFetch, resetStepFields]

theorem Operand.read_afterStep_lods_down_rax (s : RamState) (length n : Nat) (ip : BitVec 64) :
    (Operand.reg 0 : Operand 64).read (afterStep s length fun t => lodsDownSpec n { t with Next_IP := ip }) =
      mergeGPR n ((Operand.mem (rsi.read s) : Operand n).read s) ((Operand.reg 0 : Operand 64).read s) := by
  rw [Operand.read_afterStep]
  simp only [lodsDownSpec, Operand.read_write_reg_of_ne _ (show (6 : BitVec 5) ≠ 0 by decide)]
  simp [Operand.write, Operand.read, dataAccess, afterFetches, beforeFetch, resetStepFields]

theorem AgreesExcept.afterStep_lods_down (s : RamState) (length n : Nat) (ip : BitVec 64) :
    AgreesExcept [.reg 0, .reg 6, .rip] s
      (afterStep s length fun t => lodsDownSpec n { t with Next_IP := ip }) := by
  refine (AgreesExcept.of_afterStep s length _ (((((AgreesExcept.of_nextIP _ ip).trans
    (AgreesExcept.of_dataAccess _ "load")).trans
    (AgreesExcept.write_reg _ 0 _)).trans
    (AgreesExcept.write_reg _ 6 _)))).mono ?_
  intro c hc
  simp only [List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> simp

theorem ReadyToStep.afterStep_lods_down [Bindings] {s : RamState} (h : ReadyToStep s) (length n : Nat)
    (ip : BitVec 64) :
    ReadyToStep (afterStep s length fun t => lodsDownSpec n { t with Next_IP := ip }) :=
  ReadyToStep.of_agreesExcept h (AgreesExcept.afterStep_lods_down s length n ip) (by
    rw [afterStep_lods_down_external]
    exact h.memory.tables)

theorem afterStep_lods_down_seg_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length n : Nat)
    (ip : BitVec 64) {base : BitVec 64} :
    (afterStep s length fun t => lodsDownSegSpec base n { t with Next_IP := ip }).RIP = ip := by
  simp [afterStep, finishStep, lodsDownSegSpec, Operand.write, dataAccess, afterFetches,
    beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

@[simp] theorem afterStep_lods_down_seg_external (s : RamState) (length n : Nat) (ip : BitVec 64) {base : BitVec 64} :
    (afterStep s length fun t => lodsDownSegSpec base n { t with Next_IP := ip }).external = s.external := rfl

theorem Operand.read_afterStep_lods_down_seg_rsi (s : RamState) (length n : Nat) (ip : BitVec 64) {base : BitVec 64} :
    rsi.read (afterStep s length fun t => lodsDownSegSpec base n { t with Next_IP := ip }) = rsi.read s - BitVec.ofNat 64 (n / 8) := by
  rw [Operand.read_afterStep]
  simp [lodsDownSegSpec, afterFetches, beforeFetch, resetStepFields]

theorem Operand.read_afterStep_lods_down_seg_rax (s : RamState) (length n : Nat) (ip : BitVec 64) {base : BitVec 64} :
    (Operand.reg 0 : Operand 64).read (afterStep s length fun t => lodsDownSegSpec base n { t with Next_IP := ip }) =
      mergeGPR n ((Operand.mem (base + rsi.read s) : Operand n).read s) ((Operand.reg 0 : Operand 64).read s) := by
  rw [Operand.read_afterStep]
  simp only [lodsDownSegSpec, Operand.read_write_reg_of_ne _ (show (6 : BitVec 5) ≠ 0 by decide)]
  simp [Operand.write, Operand.read, dataAccess, afterFetches, beforeFetch, resetStepFields]

theorem AgreesExcept.afterStep_lods_down_seg (s : RamState) (length n : Nat) (ip : BitVec 64) {base : BitVec 64} :
    AgreesExcept [.reg 0, .reg 6, .rip] s
      (afterStep s length fun t => lodsDownSegSpec base n { t with Next_IP := ip }) := by
  refine (AgreesExcept.of_afterStep s length _ (((((AgreesExcept.of_nextIP _ ip).trans
    (AgreesExcept.of_dataAccess _ "load")).trans
    (AgreesExcept.write_reg _ 0 _)).trans
    (AgreesExcept.write_reg _ 6 _)))).mono ?_
  intro c hc
  simp only [List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> simp

theorem ReadyToStep.afterStep_lods_down_seg [Bindings] {s : RamState} (h : ReadyToStep s) (length n : Nat)
    (ip : BitVec 64) {base : BitVec 64} :
    ReadyToStep (afterStep s length fun t => lodsDownSegSpec base n { t with Next_IP := ip }) :=
  ReadyToStep.of_agreesExcept h (AgreesExcept.afterStep_lods_down_seg s length n ip) (by
    rw [afterStep_lods_down_seg_external]
    exact h.memory.tables)

theorem lodsq_down_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAD]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hrd : MemReadable s (rsi.read s) 8) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      lodsDownSpec 64 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xAD]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAD]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_AD_lodsq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [lodsq_down_form _ _ _ (memAlu_dataReady h _) haddr hrex2 hlock hw hrep hseg hm64 h.cpu.ds hdf
    (hrd.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xAD [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem lodsq_down_seg_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAD]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hrd : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 8) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      lodsDownSegSpec (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 64
        { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xAD]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAD]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_AD_lodsq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [lodsq_down_seg_form _ _ _ (memAlu_dataReady h _) haddr hrex2 hlock hw hrep hseg hsr hdf
    (hrd.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xAD [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem lodsd_down_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAD]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hrd : MemReadable s (rsi.read s) 4) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      lodsDownSpec 32 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xAD]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAD]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_AD_lodsd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [lodsd_down_form _ _ _ (memAlu_dataReady h _) haddr hrex2 hlock hosz hw hrep hseg hm64 h.cpu.ds hdf
    (hrd.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xAD [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem lodsd_down_seg_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAD]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hrd : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 4) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      lodsDownSegSpec (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 32
        { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xAD]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAD]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_AD_lodsd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [lodsd_down_seg_form _ _ _ (memAlu_dataReady h _) haddr hrex2 hlock hosz hw hrep hseg hsr hdf
    (hrd.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xAD [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem lodsw_down_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAD]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hrd : MemReadable s (rsi.read s) 2) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      lodsDownSpec 16 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xAD]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAD]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_AD_lodsw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [lodsw_down_form _ _ _ (memAlu_dataReady h _) haddr hrex2 hlock hw hrep hseg hm64 h.cpu.ds hdf
    (hrd.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xAD [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem lodsw_down_seg_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAD]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hrd : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 2) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      lodsDownSegSpec (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 16
        { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xAD]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAD]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_AD_lodsw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [lodsw_down_seg_form _ _ _ (memAlu_dataReady h _) haddr hrex2 hlock hw hrep hseg hsr hdf
    (hrd.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xAD [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem lodsb_down_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAC]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hrd : MemReadable s (rsi.read s) 1) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      lodsDownSpec 8 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xAC]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAC]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_AC_lodsb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [lodsb_down_form _ _ _ (memAlu_dataReady h _) haddr hrex2 hlock hrep hseg hm64 h.cpu.ds hdf
    (hrd.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xAC [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem lodsb_down_seg_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAC]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hrd : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 1) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      lodsDownSegSpec (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 8
        { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xAC]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAC]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_AC_lodsb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [lodsb_down_seg_form _ _ _ (memAlu_dataReady h _) haddr hrex2 hlock hrep hseg hsr hdf
    (hrd.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xAC [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

end X86Proofs
