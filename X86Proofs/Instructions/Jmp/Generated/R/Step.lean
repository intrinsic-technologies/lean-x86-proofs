import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Call.Step
import X86Proofs.Instructions.Jmp.Generated.R.Decode
import X86Proofs.Instructions.Jmp.Generated.R.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem jmp_r64_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hmode64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4)
    (hcode : BytesAt s s.RIP (pre ++ [0xFF, modrm]))
    (hlow : s.RIP.toNat + (pre.length + 2) ≤ 2^32)
    (htarget : ((Operand.reg (gprNumber (scanContext s.DS (PrefixSegments.ofState s) pre).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) pre).rex_b3 (modrmRm modrm)) : Operand 64).read s).toNat < 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let src : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2) fun t =>
      jumpState t (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2))) (src.read s))) := by
  intro ctx src
  have hlen' : (pre ++ [0xFF, modrm]).length = pre.length + 2 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xFF, modrm]).length ≤ 2^32 := by rw [hlen']; exact hlow
  have hdecode := decodeLegacy0_run_of_FF_jmp_register s h _ pre.length modrm hmod hreg hcode
    hlow' (by simp) (by simp) (by omega) ctx hrex2
  have hmode : In64BitMode (afterFetches (beforeFetch s) (pre.length + 3)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [jmp_r_form _ _ _ _ hmode64 hlock hmode (h.branchReady _) htarget] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xFF [modrm] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    (hmode.of_cs_lma_eq rfl rfl)

end X86Proofs
