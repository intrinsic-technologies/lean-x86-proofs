import X86Proofs.Step.MemOperand
import X86Proofs.Step.Decode.Legacy0Opcode88

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy0_run_of_88_memory [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm ≠ 3) (bytes : List UInt8) (k : Nat)
    (hk : k + 1 < 15) (h88 : bytes[k]? = some 0x88)
    (hm : bytes[k + 1]? = some modrm) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.MOV_MEMb_GPR8_1 (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2))) ctx
        (modrmMod modrm) (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) (k + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy0_run_of_modrm_at s h bytes k 0x88 modrm hcode hlow h88 hm hk ctx
    _ _
    (fun a u hf hmode => decodeLegacy0_run_of_opcode88 a u _ ctx hrex2 hf hmode)
    (fun a u hf hmode hfe =>
      decodeLegacy0Opcode88_run_of_memory a u _ ctx _ hmod hmode hfe hf)

end X86Proofs
