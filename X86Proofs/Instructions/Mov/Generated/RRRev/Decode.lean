import X86Proofs.Step.MemOperand
import X86Proofs.Step.Decode.Legacy0Opcode8B

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy0_run_of_8B_register [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (bytes : List UInt8) (k : Nat)
    (hk : k + 1 < 15) (h8b : bytes[k]? = some 0x8B)
    (hm : bytes[k + 1]? = some modrm) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.MOV_GPRv_GPRv_8B (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2))) ctx
        (modrmReg modrm) (modrmRm modrm)).run (afterFetches (beforeFetch s) (k + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy0_run_of_modrm_at s h bytes k 0x8B modrm hcode hlow h8b hm hk ctx
    _ _
    (fun a u hf hmode => decodeLegacy0_run_of_opcode8B a u _ ctx hrex2 hf hmode)
    (fun a u hf hmode hfe =>
      decodeLegacy0Opcode8B_run_of_register a u _ ctx _ hmod hmode hfe hf)

end X86Proofs
