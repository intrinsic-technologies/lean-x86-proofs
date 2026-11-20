
import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Popf.Generated.Stack.Decode
import X86Proofs.Instructions.Popf.Generated.Stack.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem afterStep_popfq_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (ip : BitVec 64) : (afterStep s length fun t => popfqState { t with Next_IP := ip }).RIP = ip := by
  simp [afterStep, finishStep, popfqState, Operand.write, dataAccess, afterFetches,
    beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

@[simp] theorem afterStep_popfq_external (s : RamState) (length : Nat) (ip : BitVec 64) :
    (afterStep s length fun t => popfqState { t with Next_IP := ip }).external = s.external := rfl

theorem Operand.read_afterStep_popfq_rsp (s : RamState) (length : Nat) (ip : BitVec 64) :
    (Operand.reg 4 : Operand 64).read (afterStep s length fun t => popfqState { t with Next_IP := ip }) = stackPtr s + 8 := by
  rw [Operand.read_afterStep, popfqState, Operand.read_write_reg64_self]
  rfl

theorem Operand.read_afterStep_popfq_df (s : RamState) (length : Nat) (ip : BitVec 64) :
    (Operand.df : Operand 1).read (afterStep s length fun t => popfqState { t with Next_IP := ip }) = dfBit ((Operand.mem (stackPtr s) : Operand 64).read s) := by
  simp only [Operand.read_df, afterStep, finishStep, popfqState, Operand.write_reg64]
  exact dfBit_popfSpec _ _

theorem ofRFLAGS_afterStep_popfq (s : RamState) (length : Nat) (ip : BitVec 64) :
    StatusFlags.ofRFLAGS (afterStep s length fun t => popfqState { t with Next_IP := ip }).RFLAGS = StatusFlags.ofRFLAGS ((Operand.mem (stackPtr s) : Operand 64).read s) := by
  simp only [afterStep, finishStep, popfqState, Operand.write_reg64]
  exact ofRFLAGS_popfSpec _ _

theorem AgreesExcept.afterStep_popfq (s : RamState) (length : Nat) (ip : BitVec 64)
    (hk : PopfKeeps ((Operand.mem (stackPtr s) : Operand 64).read s) s.RFLAGS) :
    AgreesExcept [.df, .reg 4, .flags, .rip] s (afterStep s length fun t => popfqState { t with Next_IP := ip }) :=
  ((AgreesExcept.prepare s (length + 1) ip).trans
    (AgreesExcept.of_popfqState _ hk)).trans (AgreesExcept.of_finishStep _)

theorem ReadyToStep.afterStep_popfq [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (ip : BitVec 64)
    (hk : PopfKeeps ((Operand.mem (stackPtr s) : Operand 64).read s) s.RFLAGS) :
    ReadyToStep (afterStep s length fun t => popfqState { t with Next_IP := ip }) :=
  h.of_agreesExcept (AgreesExcept.afterStep_popfq s length ip hk) h.memory.tables

theorem popfq_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0x9D]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hr : MemReadable s (stackPtr s) 8)
    (hiopl : X86.Runtime.Unsigned (s.RFLAGS.extractLsb' 12 2) < s.CPL) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      popfqState { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0x9D]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x9D]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hd : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl h.memory.tables
  have hdecode := decodeLegacy0_run_of_9D_popfq s h _ hrex2 hosz _ pre.length
    (by omega) (by simp) hcode hlow'
  rw [popfq_form _ _ _ hlock hd h.cpu.ss (hr.of_external_eq rfl) hiopl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x9D [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem afterStep_popf_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (ip : BitVec 64) : (afterStep s length fun t => popfState { t with Next_IP := ip }).RIP = ip := by
  simp [afterStep, finishStep, popfState, Operand.write, dataAccess, afterFetches,
    beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

@[simp] theorem afterStep_popf_external (s : RamState) (length : Nat) (ip : BitVec 64) :
    (afterStep s length fun t => popfState { t with Next_IP := ip }).external = s.external := rfl

theorem Operand.read_afterStep_popf_rsp (s : RamState) (length : Nat) (ip : BitVec 64) :
    (Operand.reg 4 : Operand 64).read (afterStep s length fun t => popfState { t with Next_IP := ip }) = stackPtr s + 2 := by
  rw [Operand.read_afterStep, popfState, Operand.read_write_reg64_self]
  rfl

theorem Operand.read_afterStep_popf_df (s : RamState) (length : Nat) (ip : BitVec 64) :
    (Operand.df : Operand 1).read (afterStep s length fun t => popfState { t with Next_IP := ip }) = dfBit (((Operand.mem (stackPtr s) : Operand 16).read s).setWidth 64) := by
  simp only [Operand.read_df, afterStep, finishStep, popfState, Operand.write_reg64]
  exact dfBit_popf16Spec _ _

theorem ofRFLAGS_afterStep_popf (s : RamState) (length : Nat) (ip : BitVec 64) :
    StatusFlags.ofRFLAGS (afterStep s length fun t => popfState { t with Next_IP := ip }).RFLAGS = StatusFlags.ofRFLAGS (((Operand.mem (stackPtr s) : Operand 16).read s).setWidth 64) := by
  simp only [afterStep, finishStep, popfState, Operand.write_reg64]
  exact ofRFLAGS_popf16Spec _ _

theorem AgreesExcept.afterStep_popf (s : RamState) (length : Nat) (ip : BitVec 64)
    (hk : Popf16Keeps ((Operand.mem (stackPtr s) : Operand 16).read s) s.RFLAGS) :
    AgreesExcept [.df, .reg 4, .flags, .rip] s (afterStep s length fun t => popfState { t with Next_IP := ip }) :=
  ((AgreesExcept.prepare s (length + 1) ip).trans
    (AgreesExcept.of_popfState _ hk)).trans (AgreesExcept.of_finishStep _)

theorem ReadyToStep.afterStep_popf [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (ip : BitVec 64)
    (hk : Popf16Keeps ((Operand.mem (stackPtr s) : Operand 16).read s) s.RFLAGS) :
    ReadyToStep (afterStep s length fun t => popfState { t with Next_IP := ip }) :=
  h.of_agreesExcept (AgreesExcept.afterStep_popf s length ip hk) h.memory.tables

theorem popf_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hcode : BytesAt s s.RIP (pre ++ [0x9D]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hr : MemReadable s (stackPtr s) 2)
    (hiopl : X86.Runtime.Unsigned (s.RFLAGS.extractLsb' 12 2) < s.CPL) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      popfState { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0x9D]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x9D]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hd : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl h.memory.tables
  have hdecode := decodeLegacy0_run_of_9D_popf s h _ hrex2 hosz hw _ pre.length
    (by omega) (by simp) hcode hlow'
  rw [popf_form _ _ _ hlock hd h.cpu.ss (hr.of_external_eq rfl) hiopl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x9D [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

end X86Proofs
