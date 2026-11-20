
import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.String
import X86Proofs.Instructions.Cmps.Generated.Str.Decode
import X86Proofs.Instructions.Cmps.Generated.Str.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem afterStep_cmps_down_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length n : Nat)
    (ip : BitVec 64) :
    (afterStep s length fun t => cmpsDownSpec n { t with Next_IP := ip }).RIP = ip := by
  simp [afterStep, finishStep, cmpsDownSpec, Operand.write, dataAccess, setFlags, afterFetches,
    beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

@[simp] theorem afterStep_cmps_down_external (s : RamState) (length n : Nat) (ip : BitVec 64) :
    (afterStep s length fun t => cmpsDownSpec n { t with Next_IP := ip }).external = s.external := rfl

theorem Operand.read_afterStep_cmps_down_rsi (s : RamState) (length n : Nat) (ip : BitVec 64) :
    rsi.read (afterStep s length fun t => cmpsDownSpec n { t with Next_IP := ip }) = rsi.read s - BitVec.ofNat 64 (n / 8) := by
  rw [Operand.read_afterStep]
  simp only [cmpsDownSpec, Operand.read_write_reg_of_ne _ (show (7 : BitVec 5) ≠ 6 by decide)]
  simp [setFlags, afterFetches, beforeFetch, resetStepFields]

theorem Operand.read_afterStep_cmps_down_rdi (s : RamState) (length n : Nat) (ip : BitVec 64) :
    rdi.read (afterStep s length fun t => cmpsDownSpec n { t with Next_IP := ip }) = rdi.read s - BitVec.ofNat 64 (n / 8) := by
  rw [Operand.read_afterStep]
  simp [cmpsDownSpec, setFlags, afterFetches, beforeFetch, resetStepFields]

theorem afterStep_cmps_down_rflags (s : RamState) (length n : Nat) (ip : BitVec 64) :
    (afterStep s length fun t => cmpsDownSpec n { t with Next_IP := ip }).RFLAGS =
      (cmpSpec ((Operand.mem (rsi.read s) : Operand n).read s)
        ((Operand.mem (rdi.read s) : Operand n).read s)).store s.RFLAGS := rfl

theorem AgreesExcept.afterStep_cmps_down (s : RamState) (length n : Nat) (ip : BitVec 64) :
    AgreesExcept [.reg 6, .reg 7, .flags, .rip] s
      (afterStep s length fun t => cmpsDownSpec n { t with Next_IP := ip }) := by
  refine (AgreesExcept.of_afterStep s length _ (((((((AgreesExcept.of_nextIP _ ip).trans
    (AgreesExcept.of_dataAccess _ "load")).trans
    (AgreesExcept.of_dataAccess _ "load")).trans
    (AgreesExcept.of_setFlags _ _)).trans
    (AgreesExcept.write_reg _ 6 _)).trans
    (AgreesExcept.write_reg _ 7 _)))).mono ?_
  intro c hc
  simp only [List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem ReadyToStep.afterStep_cmps_down [Bindings] {s : RamState} (h : ReadyToStep s) (length n : Nat)
    (ip : BitVec 64) :
    ReadyToStep (afterStep s length fun t => cmpsDownSpec n { t with Next_IP := ip }) :=
  ReadyToStep.of_agreesExcept h (AgreesExcept.afterStep_cmps_down s length n ip) (by
    rw [afterStep_cmps_down_external]
    exact h.memory.tables)

theorem afterStep_cmps_down_seg_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length n : Nat)
    (ip : BitVec 64) {base : BitVec 64} :
    (afterStep s length fun t => cmpsDownSegSpec base n { t with Next_IP := ip }).RIP = ip := by
  simp [afterStep, finishStep, cmpsDownSegSpec, Operand.write, dataAccess, setFlags, afterFetches,
    beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

@[simp] theorem afterStep_cmps_down_seg_external (s : RamState) (length n : Nat) (ip : BitVec 64) {base : BitVec 64} :
    (afterStep s length fun t => cmpsDownSegSpec base n { t with Next_IP := ip }).external = s.external := rfl

theorem Operand.read_afterStep_cmps_down_seg_rsi (s : RamState) (length n : Nat) (ip : BitVec 64) {base : BitVec 64} :
    rsi.read (afterStep s length fun t => cmpsDownSegSpec base n { t with Next_IP := ip }) = rsi.read s - BitVec.ofNat 64 (n / 8) := by
  rw [Operand.read_afterStep]
  simp only [cmpsDownSegSpec, Operand.read_write_reg_of_ne _ (show (7 : BitVec 5) ≠ 6 by decide)]
  simp [setFlags, afterFetches, beforeFetch, resetStepFields]

theorem Operand.read_afterStep_cmps_down_seg_rdi (s : RamState) (length n : Nat) (ip : BitVec 64) {base : BitVec 64} :
    rdi.read (afterStep s length fun t => cmpsDownSegSpec base n { t with Next_IP := ip }) = rdi.read s - BitVec.ofNat 64 (n / 8) := by
  rw [Operand.read_afterStep]
  simp [cmpsDownSegSpec, setFlags, afterFetches, beforeFetch, resetStepFields]

theorem afterStep_cmps_down_seg_rflags (s : RamState) (length n : Nat) (ip : BitVec 64) {base : BitVec 64} :
    (afterStep s length fun t => cmpsDownSegSpec base n { t with Next_IP := ip }).RFLAGS =
      (cmpSpec ((Operand.mem (base + rsi.read s) : Operand n).read s)
        ((Operand.mem (rdi.read s) : Operand n).read s)).store s.RFLAGS := rfl

theorem AgreesExcept.afterStep_cmps_down_seg (s : RamState) (length n : Nat) (ip : BitVec 64) {base : BitVec 64} :
    AgreesExcept [.reg 6, .reg 7, .flags, .rip] s
      (afterStep s length fun t => cmpsDownSegSpec base n { t with Next_IP := ip }) := by
  refine (AgreesExcept.of_afterStep s length _ (((((((AgreesExcept.of_nextIP _ ip).trans
    (AgreesExcept.of_dataAccess _ "load")).trans
    (AgreesExcept.of_dataAccess _ "load")).trans
    (AgreesExcept.of_setFlags _ _)).trans
    (AgreesExcept.write_reg _ 6 _)).trans
    (AgreesExcept.write_reg _ 7 _)))).mono ?_
  intro c hc
  simp only [List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem ReadyToStep.afterStep_cmps_down_seg [Bindings] {s : RamState} (h : ReadyToStep s) (length n : Nat)
    (ip : BitVec 64) {base : BitVec 64} :
    ReadyToStep (afterStep s length fun t => cmpsDownSegSpec base n { t with Next_IP := ip }) :=
  ReadyToStep.of_agreesExcept h (AgreesExcept.afterStep_cmps_down_seg s length n ip) (by
    rw [afterStep_cmps_down_seg_external]
    exact h.memory.tables)

theorem cmpsq_down_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hsrc : MemReadable s (rsi.read s) 8) (hdst : MemReadable s (rdi.read s) 8) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      cmpsDownSpec 64 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_cmpsq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [cmpsq_down_form hcm _ _ _ (memAlu_dataReady h _) (hmode _) hlock hseg hm64 hasz h.cpu.ds h.cpu.es h.ready.repeatClear hdf
    (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xA7 [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem cmpsq_down_seg_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hsrc : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 8) (hdst : MemReadable s (rdi.read s) 8) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      cmpsDownSegSpec (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 64
        { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_cmpsq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [cmpsq_down_seg_form hcm _ _ _ (memAlu_dataReady h _) (hmode _) hlock hseg hm64 hasz hsr h.cpu.es h.ready.repeatClear hdf
    (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xA7 [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem cmpsd_down_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hsrc : MemReadable s (rsi.read s) 4) (hdst : MemReadable s (rdi.read s) 4) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      cmpsDownSpec 32 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_cmpsd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [cmpsd_down_form hcm _ _ _ (memAlu_dataReady h _) (hmode _) hlock hseg hm64 hasz h.cpu.ds h.cpu.es h.ready.repeatClear hdf
    (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xA7 [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem cmpsd_down_seg_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hsrc : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 4) (hdst : MemReadable s (rdi.read s) 4) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      cmpsDownSegSpec (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 32
        { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_cmpsd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [cmpsd_down_seg_form hcm _ _ _ (memAlu_dataReady h _) (hmode _) hlock hseg hm64 hasz hsr h.cpu.es h.ready.repeatClear hdf
    (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xA7 [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem cmpsw_down_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hsrc : MemReadable s (rsi.read s) 2) (hdst : MemReadable s (rdi.read s) 2) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      cmpsDownSpec 16 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_cmpsw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [cmpsw_down_form hcm _ _ _ (memAlu_dataReady h _) (hmode _) hlock hseg hm64 hasz h.cpu.ds h.cpu.es h.ready.repeatClear hdf
    (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xA7 [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem cmpsw_down_seg_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hsrc : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 2) (hdst : MemReadable s (rdi.read s) 2) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      cmpsDownSegSpec (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 16
        { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_cmpsw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [cmpsw_down_seg_form hcm _ _ _ (memAlu_dataReady h _) (hmode _) hlock hseg hm64 hasz hsr h.cpu.es h.ready.repeatClear hdf
    (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xA7 [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem cmpsb_down_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA6]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hsrc : MemReadable s (rsi.read s) 1) (hdst : MemReadable s (rdi.read s) 1) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      cmpsDownSpec 8 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xA6]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA6]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_A6_cmpsb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [cmpsb_down_form hcm _ _ _ (memAlu_dataReady h _) (hmode _) hlock hseg hm64 hasz h.cpu.ds h.cpu.es h.ready.repeatClear hdf
    (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xA6 [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem cmpsb_down_seg_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA6]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hsrc : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 1) (hdst : MemReadable s (rdi.read s) 1) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      cmpsDownSegSpec (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 8
        { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xA6]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA6]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_A6_cmpsb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [cmpsb_down_seg_form hcm _ _ _ (memAlu_dataReady h _) (hmode _) hlock hseg hm64 hasz hsr h.cpu.es h.ready.repeatClear hdf
    (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xA6 [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

end X86Proofs
