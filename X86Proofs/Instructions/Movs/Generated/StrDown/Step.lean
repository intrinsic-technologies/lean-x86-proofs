
import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.String
import X86Proofs.Instructions.Movs.Generated.Str.Decode
import X86Proofs.Instructions.Movs.Generated.Str.Form
import X86Proofs.Instructions.Movs.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem afterStep_movs_down_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length n : Nat)
    (ip : BitVec 64) :
    (afterStep s length fun t => movsDownSpec n { t with Next_IP := ip }).RIP = ip := by
  simp [afterStep, finishStep, movsDownSpec, Operand.write, dataAccess, afterFetches,
    beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

@[simp] theorem afterStep_movs_down_external (s : RamState) (length n : Nat) (ip : BitVec 64) :
    (afterStep s length fun t => movsDownSpec n { t with Next_IP := ip }).external =
      memStore s.external (rdi.read s)
        ((Operand.mem (rsi.read s) : Operand n).read s) := rfl

theorem Operand.read_afterStep_movs_down_mem (s : RamState) (length : Nat) {n : Nat}
    (hn : n % 8 = 0) (h64 : n ≤ 128) (ip : BitVec 64) :
    (Operand.mem (rdi.read s) : Operand n).read (afterStep s length fun t => movsDownSpec n { t with Next_IP := ip }) =
      (Operand.mem (rsi.read s) : Operand n).read s := by
  simp only [Operand.read, afterStep_movs_down_external]
  exact memLoad_memStore _ _ hn h64 _

theorem Operand.read_afterStep_movs_down_rsi (s : RamState) (length n : Nat) (ip : BitVec 64) :
    rsi.read (afterStep s length fun t => movsDownSpec n { t with Next_IP := ip }) = rsi.read s - BitVec.ofNat 64 (n / 8) := by
  rw [Operand.read_afterStep]
  simp only [movsDownSpec, Operand.read_write_reg_of_ne _ (show (7 : BitVec 5) ≠ 6 by decide)]
  simp [afterFetches, beforeFetch, resetStepFields]

theorem Operand.read_afterStep_movs_down_rdi (s : RamState) (length n : Nat) (ip : BitVec 64) :
    rdi.read (afterStep s length fun t => movsDownSpec n { t with Next_IP := ip }) = rdi.read s - BitVec.ofNat 64 (n / 8) := by
  rw [Operand.read_afterStep]
  simp [movsDownSpec, afterFetches, beforeFetch, resetStepFields]

theorem AgreesExcept.afterStep_movs_down (s : RamState) (length n : Nat) (ip : BitVec 64) :
    AgreesExcept [.reg 6, .reg 7, .mem (rdi.read s) (n / 8), .rip] s
      (afterStep s length fun t => movsDownSpec n { t with Next_IP := ip }) := by
  refine (AgreesExcept.of_afterStep s length _ (((((((AgreesExcept.of_nextIP _ ip).trans
    (AgreesExcept.of_dataAccess _ "load")).trans
    (AgreesExcept.of_dataAccess _ "store")).trans
    (AgreesExcept.write_mem _ _ _)).trans
    (AgreesExcept.write_reg _ 6 _)).trans
    (AgreesExcept.write_reg _ 7 _)))).mono ?_
  intro c hc
  simp only [List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> simp [afterFetches, beforeFetch, resetStepFields]

theorem ReadyToStep.afterStep_movs_down [Bindings] {s : RamState} (h : ReadyToStep s) (length n : Nat)
    (ip : BitVec 64) (hwr : MemWritable s (rdi.read s) (n / 8)) :
    ReadyToStep (afterStep s length fun t => movsDownSpec n { t with Next_IP := ip }) :=
  ReadyToStep.of_agreesExcept h (AgreesExcept.afterStep_movs_down s length n ip) (by
    rw [afterStep_movs_down_external]
    exact IdentityPageTableMemory.memStore h.memory.tables _ _ hwr.low hwr.tables)

theorem afterStep_movs_down_seg_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length n : Nat)
    (ip : BitVec 64) {base : BitVec 64} :
    (afterStep s length fun t => movsDownSegSpec base n { t with Next_IP := ip }).RIP = ip := by
  simp [afterStep, finishStep, movsDownSegSpec, Operand.write, dataAccess, afterFetches,
    beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

@[simp] theorem afterStep_movs_down_seg_external (s : RamState) (length n : Nat) (ip : BitVec 64) {base : BitVec 64} :
    (afterStep s length fun t => movsDownSegSpec base n { t with Next_IP := ip }).external =
      memStore s.external (rdi.read s)
        ((Operand.mem (base + rsi.read s) : Operand n).read s) := rfl

theorem Operand.read_afterStep_movs_down_seg_mem (s : RamState) (length : Nat) {n : Nat}
    (hn : n % 8 = 0) (h64 : n ≤ 128) (ip : BitVec 64) {base : BitVec 64} :
    (Operand.mem (rdi.read s) : Operand n).read (afterStep s length fun t => movsDownSegSpec base n { t with Next_IP := ip }) =
      (Operand.mem (base + rsi.read s) : Operand n).read s := by
  simp only [Operand.read, afterStep_movs_down_seg_external]
  exact memLoad_memStore _ _ hn h64 _

theorem Operand.read_afterStep_movs_down_seg_rsi (s : RamState) (length n : Nat) (ip : BitVec 64) {base : BitVec 64} :
    rsi.read (afterStep s length fun t => movsDownSegSpec base n { t with Next_IP := ip }) = rsi.read s - BitVec.ofNat 64 (n / 8) := by
  rw [Operand.read_afterStep]
  simp only [movsDownSegSpec, Operand.read_write_reg_of_ne _ (show (7 : BitVec 5) ≠ 6 by decide)]
  simp [afterFetches, beforeFetch, resetStepFields]

theorem Operand.read_afterStep_movs_down_seg_rdi (s : RamState) (length n : Nat) (ip : BitVec 64) {base : BitVec 64} :
    rdi.read (afterStep s length fun t => movsDownSegSpec base n { t with Next_IP := ip }) = rdi.read s - BitVec.ofNat 64 (n / 8) := by
  rw [Operand.read_afterStep]
  simp [movsDownSegSpec, afterFetches, beforeFetch, resetStepFields]

theorem AgreesExcept.afterStep_movs_down_seg (s : RamState) (length n : Nat) (ip : BitVec 64) {base : BitVec 64} :
    AgreesExcept [.reg 6, .reg 7, .mem (rdi.read s) (n / 8), .rip] s
      (afterStep s length fun t => movsDownSegSpec base n { t with Next_IP := ip }) := by
  refine (AgreesExcept.of_afterStep s length _ (((((((AgreesExcept.of_nextIP _ ip).trans
    (AgreesExcept.of_dataAccess _ "load")).trans
    (AgreesExcept.of_dataAccess _ "store")).trans
    (AgreesExcept.write_mem _ _ _)).trans
    (AgreesExcept.write_reg _ 6 _)).trans
    (AgreesExcept.write_reg _ 7 _)))).mono ?_
  intro c hc
  simp only [List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> simp [afterFetches, beforeFetch, resetStepFields]

theorem ReadyToStep.afterStep_movs_down_seg [Bindings] {s : RamState} (h : ReadyToStep s) (length n : Nat)
    (ip : BitVec 64) {base : BitVec 64} (hwr : MemWritable s (rdi.read s) (n / 8)) :
    ReadyToStep (afterStep s length fun t => movsDownSegSpec base n { t with Next_IP := ip }) :=
  ReadyToStep.of_agreesExcept h (AgreesExcept.afterStep_movs_down_seg s length n ip) (by
    rw [afterStep_movs_down_seg_external]
    exact IdentityPageTableMemory.memStore h.memory.tables _ _ hwr.low hwr.tables)

theorem movsq_down_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hrd : MemReadable s (rsi.read s) 8) (hwr : MemWritable s (rdi.read s) 8) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      movsDownSpec 64 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_movsq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [movsq_down_form _ _ _ (memAlu_dataReady h _) (hmode _) haddr hrex2 hlock hw hrep hseg hm64 h.cpu.ds h.cpu.es hdf
    (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xA5 [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem movsq_down_seg_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hrd : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 8) (hwr : MemWritable s (rdi.read s) 8) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      movsDownSegSpec (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 64
        { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_movsq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [movsq_down_seg_form _ _ _ (memAlu_dataReady h _) (hmode _) haddr hrex2 hlock hw hrep hseg hsr h.cpu.es hdf
    (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xA5 [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem movsd_down_step [Bindings]
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
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hrd : MemReadable s (rsi.read s) 4) (hwr : MemWritable s (rdi.read s) 4) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      movsDownSpec 32 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_movsd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [movsd_down_form _ _ _ (memAlu_dataReady h _) (hmode _) haddr hrex2 hlock hosz hw hrep hseg hm64 h.cpu.ds h.cpu.es hdf
    (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xA5 [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem movsd_down_seg_step [Bindings]
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
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hrd : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 4) (hwr : MemWritable s (rdi.read s) 4) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      movsDownSegSpec (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 32
        { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_movsd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [movsd_down_seg_form _ _ _ (memAlu_dataReady h _) (hmode _) haddr hrex2 hlock hosz hw hrep hseg hsr h.cpu.es hdf
    (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xA5 [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem movsw_down_step [Bindings]
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
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hrd : MemReadable s (rsi.read s) 2) (hwr : MemWritable s (rdi.read s) 2) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      movsDownSpec 16 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_movsw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [movsw_down_form _ _ _ (memAlu_dataReady h _) (hmode _) haddr hrex2 hlock hw hrep hseg hm64 h.cpu.ds h.cpu.es hdf
    (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xA5 [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem movsw_down_seg_step [Bindings]
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
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hrd : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 2) (hwr : MemWritable s (rdi.read s) 2) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      movsDownSegSpec (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 16
        { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_movsw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [movsw_down_seg_form _ _ _ (memAlu_dataReady h _) (hmode _) haddr hrex2 hlock hw hrep hseg hsr h.cpu.es hdf
    (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xA5 [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem movsb_down_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA4]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hrd : MemReadable s (rsi.read s) 1) (hwr : MemWritable s (rdi.read s) 1) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      movsDownSpec 8 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xA4]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA4]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_A4_movsb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [movsb_down_form _ _ _ (memAlu_dataReady h _) (hmode _) haddr hrex2 hlock hrep hseg hm64 h.cpu.ds h.cpu.es hdf
    (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xA4 [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem movsb_down_seg_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagSet s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA4]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hrd : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 1) (hwr : MemWritable s (rdi.read s) 1) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      movsDownSegSpec (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 8
        { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xA4]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA4]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_A4_movsb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [movsb_down_seg_form _ _ _ (memAlu_dataReady h _) (hmode _) haddr hrex2 hlock hrep hseg hsr h.cpu.es hdf
    (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xA4 [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

end X86Proofs
