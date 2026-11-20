
import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Cmpxchg.Generated.R8.Decode
import X86Proofs.Instructions.Cmpxchg.Generated.R8.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem cmpxchg_r8_r8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hreg : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_prefix_present = true ∨
      (gprNumber (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r4 (scanContext s.DS (PrefixSegments.ofState s) pre).rex_r3
        (modrmReg modrm)).toNat < 4)
    (hrm : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_prefix_present = true ∨
      (gprNumber (scanContext s.DS (PrefixSegments.ofState s) pre).rex_b4 (scanContext s.DS (PrefixSegments.ofState s) pre).rex_b3
        (modrmRm modrm)).toNat < 4)
    (hcode : BytesAt s s.RIP (pre ++ [0x0F, 0xB0, modrm]))
    (hlow : s.RIP.toNat + (pre.length + 3) ≤ 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm))
    let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 (modrmReg modrm))
    let acc : Operand 8 := .reg 0
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3) fun t =>
      if acc.read s = dst.read s then
          writeOutputs t dst (src.read s, cmpSpec (acc.read s) (dst.read s)) 0
            (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3)))
        else
          writeOutputs t acc (dst.read s, cmpSpec (acc.read s) (dst.read s)) 0
            (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3))))) := by
  intro ctx dst src acc
  have hlen' : (pre ++ [0x0F, 0xB0, modrm]).length = pre.length + 3 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x0F, 0xB0, modrm]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy1_run_of_B0_register s h _ hrex2 modrm hmod _ (pre.length + 1)
    (by omega) (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) hcode hlow'
  rw [cmpxchg_r8_r8_form _ _ _ _ _ (hmode _) hreg hrm hlock,
    show (pre.length + 1) + 2 = pre.length + 3 by omega] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode

  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · split <;> first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_scan_legacy1 s _ h pre 0xB0 [modrm] hpre ⟨by decide, by decide⟩ (by omega) hcode
    hlow' hdecode ((hmode (pre.length + 1 + 3)).of_cs_lma_eq 
      (by dsimp only; split <;> rfl) (by dsimp only; split <;> rfl))

theorem cmpxchg_r8_r8_gpr8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP (pre ++ [0x0F, 0xB0, modrm]))
    (hlow : s.RIP.toNat + (pre.length + 3) ≤ 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let dst : Operand 8 := .gpr8 (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm)) (byteRex ctx)
    let src : Operand 8 := .gpr8 (gprNumber ctx.rex_r4 ctx.rex_r3 (modrmReg modrm)) (byteRex ctx)
    let acc : Operand 8 := .reg 0
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3) fun t =>
      if acc.read s = dst.read s then
          writeOutputs t dst (src.read s, cmpSpec (acc.read s) (dst.read s)) 0
            (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3)))
        else
          writeOutputs t acc (dst.read s, cmpSpec (acc.read s) (dst.read s)) 0
            (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3))))) := by
  intro ctx dst src acc
  have hlen' : (pre ++ [0x0F, 0xB0, modrm]).length = pre.length + 3 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x0F, 0xB0, modrm]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy1_run_of_B0_register s h _ hrex2 modrm hmod _ (pre.length + 1)
    (by omega) (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) hcode hlow'
  rw [cmpxchg_r8_r8_gpr8_form _ _ _ _ _ (hmode _) hlock,
    show (pre.length + 1) + 2 = pre.length + 3 by omega] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode

  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · split <;> first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_scan_legacy1 s _ h pre 0xB0 [modrm] hpre ⟨by decide, by decide⟩ (by omega) hcode
    hlow' hdecode ((hmode _).of_cs_lma_eq
      (by dsimp only; split <;> exact writeOutputs_CS _ _ _ _ _)
      (by dsimp only; split <;> rw [writeOutputs_IA32_EFER]))

end X86Proofs
