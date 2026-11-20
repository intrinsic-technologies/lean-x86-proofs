
import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Xchg.Generated.Acc.Decode
import X86Proofs.Instructions.Xchg.Generated.Acc.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem xchg_r_rax_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false) (op : UInt8)
    (hop : op ∈ [0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97])
    (h90 : op = 0x90 → (scanContext s.DS (PrefixSegments.ofState s) pre).rex_b3 = 1 ∧
      (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hcode : BytesAt s s.RIP (pre ++ [op])) (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let r := gprNumber ctx.rex_b4 ctx.rex_b3 (op.toBitVec.extractLsb' 0 3)
    let dst : Operand n := .reg r
    let acc : Operand n := .reg 0
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      writeResultPair t 0 r (xchgSpec (dst.read s) (acc.read s)).2
        (xchgSpec (dst.read s) (acc.read s)).1
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1))))) := by
  intro ctx r dst acc
  have hlen' : (pre ++ [op]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [op]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hlegacy : LegacyOpcode op.toBitVec := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact legacyOpcode_of_check _ ⟨by decide, by decide⟩
  have hdecode := decodeLegacy0_run_of_xchgAcc s h _ hrex2 op hop h90 _ pre.length (by omega)
    (by simp) hcode hlow'
  rw [xchg_r_rax_form _ _ _ _ (hmode _) n hn hsize hlock] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre op [] hpre hlegacy (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

theorem xchg_r16_ax_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false) (op : UInt8)
    (hop : op ∈ [0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97])
    (h90 : op = 0x90 → (scanContext s.DS (PrefixSegments.ofState s) pre).rex_b3 = 1 ∧
      (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 0)
    (hcode : BytesAt s s.RIP (pre ++ [op])) (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let r := gprNumber ctx.rex_b4 ctx.rex_b3 (op.toBitVec.extractLsb' 0 3)
    let dst : Operand 16 := .reg r
    let acc : Operand 16 := .reg 0
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      writeResultPair t 0 r (xchgSpec (dst.read s) (acc.read s)).2
        (xchgSpec (dst.read s) (acc.read s)).1
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1))))) := by
  intro ctx r dst acc
  have hlen' : (pre ++ [op]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [op]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hlegacy : LegacyOpcode op.toBitVec := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact legacyOpcode_of_check _ ⟨by decide, by decide⟩
  have hdecode := decodeLegacy0_run_of_xchgAcc s h _ hrex2 op hop h90 _ pre.length (by omega)
    (by simp) hcode hlow'
  rw [xchg_r16_ax_form _ _ _ _ (hmode _) hsize hlock] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre op [] hpre hlegacy (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

end X86Proofs
