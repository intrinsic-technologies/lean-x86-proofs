import X86Proofs.Step.MemOperand
import X86Proofs.Step.Escape
import X86Proofs.Step.Decode.Legacy1OpcodeAE
import X86Proofs.Instructions.Fence.Form

/-!
# Decoding `NP 0F AE /5`, `/6`, `/7` with a register ModRM (`LFENCE`, `MFENCE`, `SFENCE`)

`Decode_Legacy_1` on the second opcode byte `AE` at offset `j` of the instruction, a register ModRM
after it, without `66` and REP, with the CPUID feature the form needs (SSE2 for LFENCE and MFENCE,
SSE for SFENCE), from the state after `j + 1` fetches, to the call of the fence form
(`decodeLegacy1OpcodeAE_run_of_lfence` & co., `Step/Decode/Legacy1OpcodeAE.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- `Decode_Legacy_1` on `AE` with a register ModRM, `reg = 5`: `LFENCE`. -/
theorem decodeLegacy1_run_of_AE_lfence [Bindings] (s : RamState) (h : ReadyToStep s)
    (hfeat : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true)
    (bytes : List UInt8) (j : Nat) (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 5)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (hop : bytes[j]? = some 0xAE) (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false) (hrep : ctx.rep_prefix = 0) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.LFENCE (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2))) ctx).run
          (afterFetches (beforeFetch s) (j + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy1_run_of_modrm_at_controls s h bytes j 0xAE modrm hcode hlow hop hm hj
    ctx _ _ (fun a u hf hmode => decodeLegacy1_run_of_opcodeAE a u _ ctx hrex2 hmode hf)
    (fun a u hf hmode hfe hst => decodeLegacy1OpcodeAE_run_of_lfence a u _ ctx hosz hrep _
      hmod hreg hmode hfe (reportsCPUFeature_of_sameControls hst hfeat) hf)

/-- `Decode_Legacy_1` on `AE` with a register ModRM, `reg = 6`: `MFENCE`. -/
theorem decodeLegacy1_run_of_AE_mfence [Bindings] (s : RamState) (h : ReadyToStep s)
    (hfeat : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true)
    (bytes : List UInt8) (j : Nat) (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 6)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (hop : bytes[j]? = some 0xAE) (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false) (hrep : ctx.rep_prefix = 0) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.MFENCE (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2))) ctx).run
          (afterFetches (beforeFetch s) (j + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy1_run_of_modrm_at_controls s h bytes j 0xAE modrm hcode hlow hop hm hj
    ctx _ _ (fun a u hf hmode => decodeLegacy1_run_of_opcodeAE a u _ ctx hrex2 hmode hf)
    (fun a u hf hmode hfe hst => decodeLegacy1OpcodeAE_run_of_mfence a u _ ctx hosz hrep _
      hmod hreg hmode hfe (reportsCPUFeature_of_sameControls hst hfeat) hf)

/-- `Decode_Legacy_1` on `AE` with a register ModRM, `reg = 7`: `SFENCE`. -/
theorem decodeLegacy1_run_of_AE_sfence [Bindings] (s : RamState) (h : ReadyToStep s)
    (hfeat : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE_Encoding true)
    (bytes : List UInt8) (j : Nat) (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 7)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (hop : bytes[j]? = some 0xAE) (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.SFENCE (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2))) ctx).run
          (afterFetches (beforeFetch s) (j + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy1_run_of_modrm_at_controls s h bytes j 0xAE modrm hcode hlow hop hm hj
    ctx _ _ (fun a u hf hmode => decodeLegacy1_run_of_opcodeAE a u _ ctx hrex2 hmode hf)
    (fun a u hf hmode hfe hst => decodeLegacy1OpcodeAE_run_of_sfence a u _ ctx hosz _
      hmod hreg hmode hfe (reportsCPUFeature_of_sameControls hst hfeat) hf)

end X86Proofs
