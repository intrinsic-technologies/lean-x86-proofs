import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Setcc.Generated.R8.Decode
import X86Proofs.Instructions.Setcc.Generated.R8.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem setcc_r8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false) (cc : BitVec 4)
    (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hrm : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_prefix_present = true ∨
      (gprNumber (scanContext s.DS (PrefixSegments.ofState s) pre).rex_b4 (scanContext s.DS (PrefixSegments.ofState s) pre).rex_b3
        (modrmRm modrm)).toNat < 4)
    (hcode : BytesAt s s.RIP (pre ++ [0x0F, setccOpcode cc, modrm]))
    (hlow : s.RIP.toNat + (pre.length + 3) ≤ 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3) fun t =>
      writeResult t dst (setccSpec (condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS)))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3))))) := by
  intro ctx dst
  have hlen' : (pre ++ [0x0F, setccOpcode cc, modrm]).length = pre.length + 3 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x0F, setccOpcode cc, modrm]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy1_run_of_setcc_register s h _ (pre.length + 1) cc modrm hmod hcode
    hlow' (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) (by omega) _ hrex2
  rw [setcc_r8_form _ _ _ _ _ (hmode _) hrm hlock,
    show pre.length + 1 + 2 = pre.length + 3 by omega] at hdecode
  simp only [afterFetches_RFLAGS, beforeFetch_RFLAGS, setccOpcode_cc] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre (setccOpcode cc) [modrm] hpre (setccOpcode_ne cc) (by omega)
    hcode hlow' hdecode ((hmode (pre.length + 1 + 3)).of_cs_lma_eq rfl rfl)

theorem setcc_r8_gpr8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false) (cc : BitVec 4)
    (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP (pre ++ [0x0F, setccOpcode cc, modrm]))
    (hlow : s.RIP.toNat + (pre.length + 3) ≤ 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let dst : Operand 8 := .gpr8 (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm)) (byteRex ctx)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3) fun t =>
      writeResult t dst (setccSpec (condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS)))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3))))) := by
  intro ctx dst
  have hlen' : (pre ++ [0x0F, setccOpcode cc, modrm]).length = pre.length + 3 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x0F, setccOpcode cc, modrm]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy1_run_of_setcc_register s h _ (pre.length + 1) cc modrm hmod hcode
    hlow' (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) (by omega) _ hrex2
  rw [setcc_r8_gpr8_form _ _ _ _ _ (hmode _) hlock,
    show pre.length + 1 + 2 = pre.length + 3 by omega] at hdecode
  simp only [afterFetches_RFLAGS, beforeFetch_RFLAGS, setccOpcode_cc] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · simp only [writeResult, Operand.write_repeat]; exact h.ready.repeatClear
  refine step_scan_legacy1 s _ h pre (setccOpcode cc) [modrm] hpre (setccOpcode_ne cc) (by omega)
    hcode hlow' hdecode ?_
  simp only [dst, Operand.gpr8]
  split <;> exact (hmode (pre.length + 3 + 1)).of_cs_lma_eq rfl rfl

end X86Proofs
