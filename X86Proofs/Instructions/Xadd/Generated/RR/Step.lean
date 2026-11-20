
import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Xadd.Generated.RR.Decode
import X86Proofs.Instructions.Xadd.Generated.RR.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem xadd_r_r_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP (pre ++ [0x0F, 0xC1, modrm]))
    (hlow : s.RIP.toNat + (pre.length + 3) ≤ 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let dst : Operand n := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm))
    let src : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 (modrmReg modrm))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3) fun t =>
      writePairOutputs t (gprNumber ctx.rex_r4 ctx.rex_r3 (modrmReg modrm))
          (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm))
          (xaddSpec (dst.read s) (src.read s)).2.1
          (xaddSpec (dst.read s) (src.read s)).1
          (xaddSpec (dst.read s) (src.read s)).2.2 0
          (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3))))) := by
  intro ctx dst src
  have hlen' : (pre ++ [0x0F, 0xC1, modrm]).length = pre.length + 3 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x0F, 0xC1, modrm]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy1_run_of_C1_register s h _ hrex2 modrm hmod _ (pre.length + 1)
    (by omega) (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) hcode hlow'
  rw [xadd_r_r_form _ _ _ _ _ (hmode _) n hn hsize hlock,
    show (pre.length + 1) + 2 = pre.length + 3 by omega] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode

  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writePairOutputs8, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_scan_legacy1 s _ h pre 0xC1 [modrm] hpre ⟨by decide, by decide⟩ (by omega) hcode
    hlow' hdecode ((hmode (pre.length + 1 + 3)).of_cs_lma_eq rfl rfl)

theorem xadd_r16_r16_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP (pre ++ [0x0F, 0xC1, modrm]))
    (hlow : s.RIP.toNat + (pre.length + 3) ≤ 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let dst : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm))
    let src : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 (modrmReg modrm))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3) fun t =>
      writePairOutputs t (gprNumber ctx.rex_r4 ctx.rex_r3 (modrmReg modrm))
          (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm))
          (xaddSpec (dst.read s) (src.read s)).2.1
          (xaddSpec (dst.read s) (src.read s)).1
          (xaddSpec (dst.read s) (src.read s)).2.2 0
          (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3))))) := by
  intro ctx dst src
  have hlen' : (pre ++ [0x0F, 0xC1, modrm]).length = pre.length + 3 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x0F, 0xC1, modrm]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy1_run_of_C1_register s h _ hrex2 modrm hmod _ (pre.length + 1)
    (by omega) (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) hcode hlow'
  rw [xadd_r16_r16_form _ _ _ _ _ (hmode _) hsize hlock,
    show (pre.length + 1) + 2 = pre.length + 3 by omega] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode

  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writePairOutputs8, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_scan_legacy1 s _ h pre 0xC1 [modrm] hpre ⟨by decide, by decide⟩ (by omega) hcode
    hlow' hdecode ((hmode (pre.length + 1 + 3)).of_cs_lma_eq rfl rfl)

end X86Proofs
