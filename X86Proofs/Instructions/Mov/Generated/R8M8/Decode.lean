import X86Proofs.Step.MemOperand
import X86Proofs.Step.Decode.Legacy0Opcode8A

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy0_run_of_8A_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm ≠ 3) (bytes : List UInt8) (k : Nat)
    (hk : k + 1 < 15) (h8a : bytes[k]? = some 0x8A)
    (hm : bytes[k + 1]? = some modrm) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.MOV_GPR8_MEMb_1 (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2))) ctx
        (modrmMod modrm) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) (k + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy0_run_of_modrm_at s h bytes k 0x8A modrm hcode hlow h8a hm hk ctx
    _ _
    (fun a u hf hmode => decodeLegacy0_run_of_opcode8A a u _ ctx hrex2 hf hmode)
    (fun a u hf hmode hfe =>
      decodeLegacy0Opcode8A_run_of_memory a u _ ctx _ hmod hmode hfe hf)

end X86Proofs
