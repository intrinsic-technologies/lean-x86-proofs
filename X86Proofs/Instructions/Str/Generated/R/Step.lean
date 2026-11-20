import X86Proofs.Step.AfterStep
import X86Proofs.Step.MemOperand
import X86Proofs.Instructions.Str.Generated.R.Decode
import X86Proofs.Instructions.Str.Generated.R.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem str_r_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8) (n : Nat)
    (hn : n = 64 ∨ n = 32 ∨ n = 16)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hsys : SysRegReadable s)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1)
    (hcode : BytesAt s s.RIP (pre ++ [0x0F, 0x00, modrm]))
    (hlow : s.RIP.toNat + (pre.length + 3) ≤ 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let dst : Operand n := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3) fun t =>
      writeResult t dst (strSpec n s.TR.selector)
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3))))) := by
  intro ctx dst
  have hlen' : (pre ++ [0x0F, 0x00, modrm]).length = pre.length + 3 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x0F, 0x00, modrm]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hcr0 (k : Nat) : Prelude.SupportedIntegerCR0 (afterFetches (beforeFetch s) k).CR0 :=
    h.cpu.cr0
  have hlma (k : Nat) : (afterFetches (beforeFetch s) k).IA32_EFER.LMA = 1 := h.cpu.efer.lma
  have hsys' (k : Nat) : SysRegReadable (afterFetches (beforeFetch s) k) := hsys.of_eq rfl rfl
  have hdecode := decodeLegacy1_run_of_00_str_register s h _ hrex2 modrm hmod hreg _
    (pre.length + 1) (by omega) (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _)
    hcode hlow'
  rw [str_r_form _ _ _ _ (hmode _) (hcr0 _) (hlma _) (hsys' _) n hn hsize hlock,
    show (pre.length + 1) + 2 = pre.length + 3 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0x00 [modrm] hpre ⟨by decide, by decide⟩ (by omega)
    hcode hlow' hdecode ((hmode (pre.length + 1 + 3)).of_cs_lma_eq rfl rfl)

end X86Proofs
