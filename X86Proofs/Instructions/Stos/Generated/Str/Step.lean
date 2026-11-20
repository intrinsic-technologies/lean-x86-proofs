
import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.String
import X86Proofs.Instructions.Stos.Generated.Str.Decode
import X86Proofs.Instructions.Stos.Generated.Str.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem afterStep_stos_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length n : Nat)
    (ip : BitVec 64) :
    (afterStep s length fun t => stosSpec n { t with Next_IP := ip }).RIP = ip := by
  simp [afterStep, finishStep, stosSpec, Operand.write, dataAccess, afterFetches,
    beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

@[simp] theorem afterStep_stos_external (s : RamState) (length n : Nat) (ip : BitVec 64) :
    (afterStep s length fun t => stosSpec n { t with Next_IP := ip }).external =
      memStore s.external (rdi.read s)
        ((Operand.reg 0 : Operand n).read s) := rfl

theorem Operand.read_afterStep_stos_mem (s : RamState) (length : Nat) {n : Nat}
    (hn : n % 8 = 0) (h64 : n ≤ 128) (ip : BitVec 64) :
    (Operand.mem (rdi.read s) : Operand n).read (afterStep s length fun t => stosSpec n { t with Next_IP := ip }) =
      (Operand.reg 0 : Operand n).read s := by
  simp only [Operand.read, afterStep_stos_external]
  exact memLoad_memStore _ _ hn h64 _

theorem Operand.read_afterStep_stos_rdi (s : RamState) (length n : Nat) (ip : BitVec 64) :
    rdi.read (afterStep s length fun t => stosSpec n { t with Next_IP := ip }) = rdi.read s + BitVec.ofNat 64 (n / 8) := by
  rw [Operand.read_afterStep]
  simp [stosSpec, afterFetches, beforeFetch, resetStepFields]

theorem AgreesExcept.afterStep_stos (s : RamState) (length n : Nat) (ip : BitVec 64) :
    AgreesExcept [.reg 7, .mem (rdi.read s) (n / 8), .rip] s
      (afterStep s length fun t => stosSpec n { t with Next_IP := ip }) := by
  refine (AgreesExcept.of_afterStep s length _ (((((AgreesExcept.of_nextIP _ ip).trans
    (AgreesExcept.of_dataAccess _ "store")).trans
    (AgreesExcept.write_mem _ _ _)).trans
    (AgreesExcept.write_reg _ 7 _)))).mono ?_
  intro c hc
  simp only [List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> simp [afterFetches, beforeFetch, resetStepFields]

theorem ReadyToStep.afterStep_stos [Bindings] {s : RamState} (h : ReadyToStep s) (length n : Nat)
    (ip : BitVec 64) (hwr : MemWritable s (rdi.read s) (n / 8)) :
    ReadyToStep (afterStep s length fun t => stosSpec n { t with Next_IP := ip }) :=
  ReadyToStep.of_agreesExcept h (AgreesExcept.afterStep_stos s length n ip) (by
    rw [afterStep_stos_external]
    exact IdentityPageTableMemory.memStore h.memory.tables _ _ hwr.low hwr.tables)

theorem stosq_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAB]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hwr : MemWritable s (rdi.read s) 8) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      stosSpec 64 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xAB]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAB]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_AB_stosq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [stosq_form _ _ _ (memAlu_dataReady h _) (hmode _) haddr hrex2 hlock hw hrep h.cpu.es hdf
    (hwr.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xAB [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem stosd_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAB]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hwr : MemWritable s (rdi.read s) 4) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      stosSpec 32 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xAB]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAB]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_AB_stosd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [stosd_form _ _ _ (memAlu_dataReady h _) (hmode _) haddr hrex2 hlock hosz hw hrep h.cpu.es hdf
    (hwr.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xAB [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem stosw_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAB]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hwr : MemWritable s (rdi.read s) 2) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      stosSpec 16 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xAB]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAB]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_AB_stosw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [stosw_form _ _ _ (memAlu_dataReady h _) (hmode _) haddr hrex2 hlock hw hrep h.cpu.es hdf
    (hwr.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xAB [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem stosb_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAA]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hwr : MemWritable s (rdi.read s) 1) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      stosSpec 8 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xAA]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAA]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_AA_stosb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [stosb_form _ _ _ (memAlu_dataReady h _) (hmode _) haddr hrex2 hlock hrep h.cpu.es hdf
    (hwr.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xAA [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem stosq_a32_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAB]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hwr : MemWritable s (rdi.read s) 8)
    (hdl : (rdi.read s).toNat + 8 < 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      stosSpec 64 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xAB]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAB]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_AB_stosq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [stosq_a32_form _ _ _ (memAlu_dataReady h _) (hmode _) haddr hrex2 hlock hw hrep h.cpu.es hdf
    (hwr.of_external_eq rfl) hdl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xAB [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem stosd_a32_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAB]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hwr : MemWritable s (rdi.read s) 4)
    (hdl : (rdi.read s).toNat + 4 < 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      stosSpec 32 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xAB]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAB]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_AB_stosd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [stosd_a32_form _ _ _ (memAlu_dataReady h _) (hmode _) haddr hrex2 hlock hosz hw hrep h.cpu.es hdf
    (hwr.of_external_eq rfl) hdl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xAB [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem stosw_a32_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAB]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hwr : MemWritable s (rdi.read s) 2)
    (hdl : (rdi.read s).toNat + 2 < 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      stosSpec 16 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xAB]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAB]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_AB_stosw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [stosw_a32_form _ _ _ (memAlu_dataReady h _) (hmode _) haddr hrex2 hlock hw hrep h.cpu.es hdf
    (hwr.of_external_eq rfl) hdl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xAB [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem stosb_a32_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAA]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hwr : MemWritable s (rdi.read s) 1)
    (hdl : (rdi.read s).toNat + 1 < 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      stosSpec 8 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xAA]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAA]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_AA_stosb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [stosb_a32_form _ _ _ (memAlu_dataReady h _) (hmode _) haddr hrex2 hlock hrep h.cpu.es hdf
    (hwr.of_external_eq rfl) hdl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xAA [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

end X86Proofs
