import X86Proofs.Step.MemOperand
import X86Proofs.Step.Escape
import X86Proofs.Step.Decode.Legacy1Opcode90

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy1_run_of_setcc_register [Bindings] (s : RamState) (h : ReadyToStep s)
    (bytes : List UInt8) (j : Nat) (cc : BitVec 4) (modrm : UInt8)
    (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (hop : bytes[j]? = some (setccOpcode cc)) (hm : bytes[j + 1]? = some modrm) (hj : j + 1 < 15)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((X86.Instructions.SETO_GPR8 (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2))) ctx
        (modrmRm modrm) (setccOpcode cc).toBitVec).run
          (afterFetches (beforeFetch s) (j + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy1_run_of_modrm_at s h bytes j (setccOpcode cc) modrm hcode hlow hop hm hj ctx
    _ _ (fun a u hf hmode =>
      decodeLegacy1_run_of_setccOpcode a u _ ctx hrex2 hmode _ (setccOpcode_mem cc) hf)
    (fun a u hf hmode hfe =>
      decodeLegacy1Opcode90_run_of_register a u _ ctx _ _ hmod hmode hfe hf)

end X86Proofs
