import X86Proofs.Step.MemOperand
import X86Proofs.Step.Escape
import X86Proofs.Step.Decode.Legacy1OpcodeC7

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy1_run_of_C7_r1_memory_w [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcx : Prelude.ReportsCPUFeature Bindings.processor s CPUID_CMPXCHG16B_Encoding true)
    (bytes : List UInt8) (j : Nat) (modrm : UInt8) (hmod : modrmMod modrm ≠ 3)
    (hreg : modrmReg modrm = 1)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (hop : bytes[j]? = some 0xC7) (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hw : ctx.rex_w = 1) (hlock : ctx.lock_prefix_present = false) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.CMPXCHG16B_MEMdq (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2))) ctx
        (modrmMod modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) (j + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy1_run_of_modrm_at_controls s h bytes j 0xC7 modrm hcode hlow hop hm hj ctx _ _
    (fun a u hf hmode => decodeLegacy1_run_of_opcodeC7 a u _ ctx hrex2 hmode hf)
    (fun a u hf hmode hfe hst =>
      decodeLegacy1OpcodeC7_run_of_r1_memory_w a u _ ctx _ hmod hreg hw hlock hmode hfe
        (reportsCPUFeature_of_sameControls hst hcx) hf)

end X86Proofs
