import X86Proofs.Step.MemOperand
import X86Proofs.Step.Decode.Legacy0
import X86Proofs.Step.Decode.Legacy0OpcodeDE

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy0_run_of_fimul_m16 [Bindings] (s : RamState) (h : ReadyToStep s)
    (bytes : List UInt8) (j : Nat) (modrm : UInt8)
    (hmod : modrmMod modrm ≠ 3) (hreg : modrmReg modrm = 1)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (hop : bytes[j]? = some 0xDE) (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      (X86.Instructions.FIMUL_ST0_MEMmem16int (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2))) ctx
        (modrmMod modrm) (modrmReg modrm) (modrmRm modrm) 0xDE).run
          (afterFetches (beforeFetch s) (j + 3)) := by
  rw [← add_ofNat_add]
  exact decodeLegacy0_run_of_modrm_at_partial s h bytes j 0xDE modrm hcode hlow hop hm hj
    ctx _ _ (fun a u hf hmode => decodeLegacy0_run_of_opcodeDE a u _ ctx hrex2 hf hmode)
    (fun a u hf hmode hfe => decodeLegacy0OpcodeDE_run_of_r1_memory a u _ ctx _ hmod
      hreg hmode hfe hf)

end X86Proofs
