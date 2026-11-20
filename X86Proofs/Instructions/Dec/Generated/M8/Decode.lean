import X86Proofs.Step.MemOperand
import X86Proofs.Step.Decode.Legacy0OpcodeFE

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy0_run_of_FE_dec_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (bytes : List UInt8) (j : Nat) (modrm : UInt8) (hmod : modrmMod modrm ≠ 3)
    (hreg : modrmReg modrm = 1) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) (hop : bytes[j]? = some 0xFE)
    (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15) (ctx : Instruction_Context)
    (hrex2 : ctx.rex2_prefix_present = false) (hlock : ctx.lock_prefix_present = false) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.DEC_MEMb (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2))) ctx
        (modrmMod modrm) (modrmRm modrm)).run (afterFetches (beforeFetch s) (j + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy0_run_of_modrm_at s h bytes j 0xFE modrm hcode hlow hop hm hj ctx _ _
    (fun a u hf hmode => decodeLegacy0_run_of_opcodeFE a u _ ctx hrex2 hf hmode)
    (fun a u hf hmode hfe =>
      decodeLegacy0OpcodeFE_run_of_dec_memory a u _ ctx _ hmod hreg hlock hmode hfe hf)

end X86Proofs
