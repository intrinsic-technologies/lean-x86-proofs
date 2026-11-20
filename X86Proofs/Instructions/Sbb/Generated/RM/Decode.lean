import X86Proofs.Step.MemOperand
import X86Proofs.Step.Decode.Legacy0Opcode1B

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy0_run_of_1B_memory [Bindings] (s : RamState) (h : ReadyToStep s) (bytes : List UInt8)
    (j : Nat) (modrm : UInt8) (hmod : modrmMod modrm ≠ 3) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) (hop : bytes[j]? = some 0x1B)
    (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15) (ctx : Instruction_Context)
    (hrex2 : ctx.rex2_prefix_present = false) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.SBB_GPRv_MEMv (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2))) ctx
        (modrmMod modrm) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) (j + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy0_run_of_modrm_at s h bytes j 0x1B modrm hcode hlow hop hm hj ctx _ _
    (fun a u hf hmode => decodeLegacy0_run_of_opcode1B a u _ ctx hrex2 hf hmode)
    (fun a u hf hmode hfe => decodeLegacy0Opcode1B_run_of_memory a u _ ctx _ hmod hmode hfe hf)

end X86Proofs
