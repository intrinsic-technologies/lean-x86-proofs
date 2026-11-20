import X86Proofs.Step.MemOperand
import X86Proofs.Step.Escape
import X86Proofs.Step.Decode.Legacy1OpcodeBF

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy1_run_of_BF_register [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (bytes : List UInt8) (k : Nat)
    (hk : k + 1 < 15) (hbf : bytes[k]? = some 0xBF)
    (hm : bytes[k + 1]? = some modrm) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some ((X86.Instructions.MOVSX_GPRv_GPR16 (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2))) ctx
        (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) (k + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy1_run_of_modrm_at s h bytes k 0xBF modrm hcode hlow hbf hm hk ctx _ _
    (fun a u hf hmode => decodeLegacy1_run_of_opcodeBF a u _ ctx hrex2 hmode hf)
    (fun a u hf hmode hfe =>
      decodeLegacy1OpcodeBF_run_of_register a u _ ctx _ hmod hmode hfe hf)

end X86Proofs
