import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Nop.Step
import X86Proofs.Instructions.Nop.Generated.R1A.Decode
import X86Proofs.Instructions.Nop.Generated.R1A.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem nop_1a_r_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [0x0F, 0x1A, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    X86.Machine.step s =
      some (.next (afterStep s 3 fun t => withNextIP t (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy1_run_of_0F_1A_nop_register s h modrm hmod hcode hlow
  rw [nop_1a_r_form _ _ _ rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy1 s _ h 0x1A [modrm] (by decide) hcode hlow hdecode
    (in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma)

end X86Proofs
