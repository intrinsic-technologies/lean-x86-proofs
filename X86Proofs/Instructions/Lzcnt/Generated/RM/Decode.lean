import X86Proofs.Step.MemOperand
import X86Proofs.Step.Escape
import X86Proofs.Step.Decode.Legacy1OpcodeBD

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy1_run_of_BD_lzcnt_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (hl : Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
    (bytes : List UInt8) (j : Nat) (modrm : UInt8) (hmod : modrmMod modrm ≠ 3)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (hop : bytes[j]? = some 0xBD) (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hrep : ctx.rep_prefix = 243) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.LZCNT_GPRv_MEMv (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2))) ctx
        (modrmMod modrm) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) (j + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy1_run_of_modrm_at_controls s h bytes j 0xBD modrm hcode hlow hop hm hj ctx _ _
    (fun a u hf hmode => decodeLegacy1_run_of_opcodeBD a u _ ctx hrex2 hmode hf)
    (fun a u hf hmode hfe hst =>
      decodeLegacy1OpcodeBD_run_of_lzcnt_memory a u _ ctx _ hmod hrep hmode hfe
        (reportsCPUFeature_of_sameControls hst hl) hf)

end X86Proofs
