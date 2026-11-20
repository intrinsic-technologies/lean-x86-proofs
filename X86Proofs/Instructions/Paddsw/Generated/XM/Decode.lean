import X86Proofs.Step.MemOperand
import X86Proofs.Step.Escape
import X86Proofs.Step.Decode.Legacy1OpcodeED

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy1_run_of_ED_66_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (hfeat : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true)
    (bytes : List UInt8) (j : Nat) (modrm : UInt8)
    (hmod : modrmMod modrm ≠ 3)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (hop : bytes[j]? = some 0xED) (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hosz : ctx.osz_prefix_present = true) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.PADDSW_XMMdq_MEMdq
        (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2))) ctx (modrmMod modrm) (modrmReg modrm)
        (modrmRm modrm)).run
          (afterFetches (beforeFetch s) (j + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy1_run_of_modrm_at_controls s h bytes j 0xED modrm hcode hlow hop hm hj
    ctx _ _ (fun a u hf hmode => decodeLegacy1_run_of_opcodeED a u _ ctx hrex2 hmode hf)
    (fun a u hf hmode hfe hst => decodeLegacy1OpcodeED_run_of_66_memory a u _ ctx hosz _
      hmod hmode hfe (reportsCPUFeature_of_sameControls hst hfeat) hf)

end X86Proofs
