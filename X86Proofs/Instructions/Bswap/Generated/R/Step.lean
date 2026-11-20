
import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Bswap.Generated.R.Decode
import X86Proofs.Instructions.Bswap.Generated.R.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem bswap_r_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13) (n : Nat)
    (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false) (op : UInt8)
    (hop : op ∈ [0xC8, 0xC9, 0xCA, 0xCB, 0xCC, 0xCD, 0xCE, 0xCF])
    (hcode : BytesAt s s.RIP (pre ++ [0x0F, op])) (hlow : s.RIP.toNat + (pre.length + 2) ≤ 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let dst : Operand n := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (op.toBitVec.extractLsb' 0 3))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2) fun t =>
      writeResult t dst (bswapSpec (dst.read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2))))) := by
  intro ctx dst
  have hlen' : (pre ++ [0x0F, op]).length = pre.length + 2 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x0F, op]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hop2 : op ≠ 0x38 ∧ op ≠ 0x3A := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hdecode := decodeLegacy1_run_of_bswap s h _ hrex2 op hop _ (pre.length + 1) (by omega)
    (by simp) hcode hlow'
  rw [bswap_r_form _ _ _ _ (hmode _) n hn hsize hlock,
    show pre.length + 1 + 1 = pre.length + 2 by omega] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre op [] hpre hop2 (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 3)).of_cs_lma_eq rfl rfl)

end X86Proofs
