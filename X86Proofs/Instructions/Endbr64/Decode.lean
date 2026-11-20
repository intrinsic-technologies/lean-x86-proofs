import X86Proofs.Step.MemOperand
import X86Proofs.Step.Escape
import X86Proofs.Step.Decode.Legacy1Opcode1E
import X86Proofs.Instructions.Endbr64.Form

/-!
# Decoding `F3 0F 1E FA` (`ENDBR64`)

`Decode_Legacy_1` on the second opcode byte `1E` at offset `j` of the instruction, ModRM `FA`
after it, with `F3`, from the state after `j + 1` fetches, to the call of `ENDBR64` if CPUID
reports CET_SS (`cet = true`) and of the reserved NOP `NOP_GPRv_GPRv_0F1E` otherwise
(`decodeLegacy1Opcode1E_run_of_endbr64`, `Step/Decode/Legacy1Opcode1E.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- `Decode_Legacy_1` on `1E` with ModRM `FA` after `F3`: `ENDBR64` with CET_SS reported, else
`NOP_GPRv_GPRv_0F1E`. -/
theorem decodeLegacy1_run_of_endbr64 [Bindings] (s : RamState) (h : ReadyToStep s) (cet : Bool)
    (hc : Prelude.ReportsCPUFeature Bindings.processor s CPUID_CET_SS_Encoding cet)
    (bytes : List UInt8) (j : Nat) (hcode : BytesAt s s.RIP bytes)
    (hlow : s.RIP.toNat + bytes.length ≤ 2^32) (hop : bytes[j]? = some 0x1E)
    (hm : bytes[j + 1]? = some 0xFA) (hj : j + 1 < 15) (ctx : Instruction_Context)
    (hrex2 : ctx.rex2_prefix_present = false) (hrep : ctx.rep_prefix = 243) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 j)) ctx).run
        (afterFetches (beforeFetch s) (j + 1)) =
      some ((if cet then X86.Instructions.ENDBR64 (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2))) ctx
        else X86.Instructions.NOP_GPRv_GPRv_0F1E (BitVec.add s.RIP (BitVec.ofNat 64 (j + 2)))
          ctx).run (afterFetches (beforeFetch s) (j + 3))) := by
  rw [← add_ofNat_add]
  exact decodeLegacy1_run_of_modrm_at_controls s h bytes j 0x1E 0xFA hcode hlow hop hm hj
    ctx _ _ (fun a u hf hmode => decodeLegacy1_run_of_opcode1E a u _ ctx hrex2 hmode hf)
    (fun a u hf hmode hfe hst => decodeLegacy1Opcode1E_run_of_endbr64 a u _ ctx hrep hmode hfe
      cet (reportsCPUFeature_of_sameControls hst hc) hf)

end X86Proofs
