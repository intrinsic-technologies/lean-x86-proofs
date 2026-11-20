import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Nop.Step
import X86Proofs.Instructions.Nop.Generated.R18r2.Decode
import X86Proofs.Instructions.Nop.Generated.R18r2.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem nop_18r2_r_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2)
    (hcode : BytesAt s s.RIP [0x0F, 0x18, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    X86.Machine.step s =
      some (.next (afterStep s 3 fun t => withNextIP t (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy1_run_of_0F_18_r2_register s h modrm hmod hreg hcode hlow
  rw [nop_18r2_r_form _ _ _ rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy1 s _ h 0x18 [modrm] (by decide) hcode hlow hdecode
    (in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma)

end X86Proofs
