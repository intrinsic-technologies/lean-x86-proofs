
import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Xchg.Generated.R8.Decode
import X86Proofs.Instructions.Xchg.Generated.R8.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem xchg_r8_r8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
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
    (hcode : BytesAt s s.RIP (pre ++ [0x86, modrm]))
    (hlow : s.RIP.toNat + (pre.length + 2) ≤ 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm))
    let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 (modrmReg modrm))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2) fun t =>
      writeResultPair t (gprNumber ctx.rex_r4 ctx.rex_r3 (modrmReg modrm))
          (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm))
          (xchgSpec (dst.read s) (src.read s)).2
          (xchgSpec (dst.read s) (src.read s)).1
          (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2))))) := by
  intro ctx dst src
  have hlen' : (pre ++ [0x86, modrm]).length = pre.length + 2 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x86, modrm]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_86_register s h _ hrex2 modrm hmod _ pre.length
    (by omega) (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) hcode hlow'
  rw [xchg_r8_r8_form _ _ _ _ _ (hmode _) hreg hrm hlock,
    show pre.length + 2 = pre.length + 2 by omega] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode

  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeResultPair8, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_scan_legacy0 s _ h pre 0x86 [modrm] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 3)).of_cs_lma_eq rfl rfl)

theorem xchg_r8_r8_gpr8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP (pre ++ [0x86, modrm]))
    (hlow : s.RIP.toNat + (pre.length + 2) ≤ 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let dst : Operand 8 := .gpr8 (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm)) (byteRex ctx)
    let src : Operand 8 := .gpr8 (gprNumber ctx.rex_r4 ctx.rex_r3 (modrmReg modrm)) (byteRex ctx)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2) fun t =>
      writeResultPair8 t src dst
        (xchgSpec (dst.read s) (src.read s)).2 (xchgSpec (dst.read s) (src.read s)).1
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2))))) := by
  intro ctx dst src
  have hlen' : (pre ++ [0x86, modrm]).length = pre.length + 2 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x86, modrm]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_86_register s h _ hrex2 modrm hmod _ pre.length
    (by omega) (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) hcode hlow'
  rw [xchg_r8_r8_gpr8_form _ _ _ _ _ (hmode _) hlock,
    show pre.length + 2 = pre.length + 2 by omega] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode

  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeResultPair8, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_scan_legacy0 s _ h pre 0x86 [modrm] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode _).writeResultPair8 _ _ _ _ _)

end X86Proofs
