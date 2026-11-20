
import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.String
import X86Proofs.Instructions.Scas.Generated.Str.Decode
import X86Proofs.Instructions.Scas.Generated.Str.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem afterStep_scas_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length n : Nat)
    (ip : BitVec 64) :
    (afterStep s length fun t => scasSpec n { t with Next_IP := ip }).RIP = ip := by
  simp [afterStep, finishStep, scasSpec, Operand.write, dataAccess, setFlags, afterFetches,
    beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

@[simp] theorem afterStep_scas_external (s : RamState) (length n : Nat) (ip : BitVec 64) :
    (afterStep s length fun t => scasSpec n { t with Next_IP := ip }).external = s.external := rfl

theorem Operand.read_afterStep_scas_rdi (s : RamState) (length n : Nat) (ip : BitVec 64) :
    rdi.read (afterStep s length fun t => scasSpec n { t with Next_IP := ip }) = rdi.read s + BitVec.ofNat 64 (n / 8) := by
  rw [Operand.read_afterStep]
  simp [scasSpec, setFlags, afterFetches, beforeFetch, resetStepFields]

theorem afterStep_scas_rflags (s : RamState) (length n : Nat) (ip : BitVec 64) :
    (afterStep s length fun t => scasSpec n { t with Next_IP := ip }).RFLAGS =
      (cmpSpec ((Operand.reg 0 : Operand n).read s)
        ((Operand.mem (rdi.read s) : Operand n).read s)).store s.RFLAGS := rfl

theorem AgreesExcept.afterStep_scas (s : RamState) (length n : Nat) (ip : BitVec 64) :
    AgreesExcept [.reg 7, .flags, .rip] s
      (afterStep s length fun t => scasSpec n { t with Next_IP := ip }) := by
  refine (AgreesExcept.of_afterStep s length _ (((((AgreesExcept.of_nextIP _ ip).trans
    (AgreesExcept.of_dataAccess _ "load")).trans
    (AgreesExcept.write_reg _ 7 _)).trans
    (AgreesExcept.of_setFlags _ _)))).mono ?_
  intro c hc
  simp only [List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> simp

theorem ReadyToStep.afterStep_scas [Bindings] {s : RamState} (h : ReadyToStep s) (length n : Nat)
    (ip : BitVec 64) :
    ReadyToStep (afterStep s length fun t => scasSpec n { t with Next_IP := ip }) :=
  ReadyToStep.of_agreesExcept h (AgreesExcept.afterStep_scas s length n ip) (by
    rw [afterStep_scas_external]
    exact h.memory.tables)

theorem scasq_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAF]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hrd : MemReadable s (rdi.read s) 8) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      scasSpec 64 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xAF]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAF]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_AF_scasq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [scasq_form _ _ _ (memAlu_dataReady h _) (hmode _) haddr hrex2 hlock hw hrep h.cpu.es hdf
    (hrd.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xAF [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem scasd_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAF]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hrd : MemReadable s (rdi.read s) 4) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      scasSpec 32 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xAF]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAF]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_AF_scasd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [scasd_form _ _ _ (memAlu_dataReady h _) (hmode _) haddr hrex2 hlock hosz hw hrep h.cpu.es hdf
    (hrd.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xAF [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem scasw_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAF]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hrd : MemReadable s (rdi.read s) 2) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      scasSpec 16 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xAF]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAF]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_AF_scasw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [scasw_form _ _ _ (memAlu_dataReady h _) (hmode _) haddr hrex2 hlock hw hrep h.cpu.es hdf
    (hrd.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xAF [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem scasb_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAE]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hrd : MemReadable s (rdi.read s) 1) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      scasSpec 8 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xAE]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAE]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_AE_scasb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [scasb_form _ _ _ (memAlu_dataReady h _) (hmode _) haddr hrex2 hlock hrep h.cpu.es hdf
    (hrd.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xAE [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem scasq_a32_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAF]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hrd : MemReadable s (rdi.read s) 8)
    (hdl : (rdi.read s).toNat + 8 < 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      scasSpec 64 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xAF]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAF]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_AF_scasq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [scasq_a32_form _ _ _ (memAlu_dataReady h _) (hmode _) haddr hrex2 hlock hw hrep h.cpu.es hdf
    (hrd.of_external_eq rfl) hdl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xAF [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem scasd_a32_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAF]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hrd : MemReadable s (rdi.read s) 4)
    (hdl : (rdi.read s).toNat + 4 < 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      scasSpec 32 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xAF]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAF]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_AF_scasd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [scasd_a32_form _ _ _ (memAlu_dataReady h _) (hmode _) haddr hrex2 hlock hosz hw hrep h.cpu.es hdf
    (hrd.of_external_eq rfl) hdl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xAF [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem scasw_a32_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAF]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hrd : MemReadable s (rdi.read s) 2)
    (hdl : (rdi.read s).toNat + 2 < 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      scasSpec 16 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xAF]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAF]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_AF_scasw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [scasw_a32_form _ _ _ (memAlu_dataReady h _) (hmode _) haddr hrex2 hlock hw hrep h.cpu.es hdf
    (hrd.of_external_eq rfl) hdl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xAF [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem scasb_a32_step [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xAE]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hrd : MemReadable s (rdi.read s) 1)
    (hdl : (rdi.read s).toNat + 1 < 2^32) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      scasSpec 8 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xAE]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xAE]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_AE_scasb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [scasb_a32_form _ _ _ (memAlu_dataReady h _) (hmode _) haddr hrex2 hlock hrep h.cpu.es hdf
    (hrd.of_external_eq rfl) hdl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_scan_legacy0 s _ h pre 0xAE [] hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
      (by omega) hcode hlow' hdecode ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

end X86Proofs
