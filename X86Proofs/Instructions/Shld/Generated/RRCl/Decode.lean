import X86Proofs.Step.MemOperand
import X86Proofs.Step.Escape
import X86Proofs.Step.Decode.Legacy1OpcodeA5

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy1_run_of_A5_register [Bindings] (s : RamState) (h : ReadyToStep s)
    (bytes : List UInt8) (j : Nat) (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (hop : bytes[j]? = some 0xA5) (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.SHLD_GPRv_GPRv_CL (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2))) ctx
        (modrmReg modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) (j + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy1_run_of_modrm_at s h bytes j 0xA5 modrm hcode hlow hop hm hj ctx _ _
    (fun a u hf hmode => decodeLegacy1_run_of_opcodeA5 a u _ ctx hrex2 hmode hf)
    (fun a u hf hmode hfe =>
      decodeLegacy1OpcodeA5_run_of_register a u _ ctx _ hmod hmode hfe hf)

end X86Proofs
