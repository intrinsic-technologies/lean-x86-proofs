
import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.String
import X86Proofs.Instructions.Xlat.Generated.Table.Decode
import X86Proofs.Instructions.Xlat.Generated.Table.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem afterStep_xlat_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (ip : BitVec 64) :
    (afterStep s length fun t => xlatSpec { t with Next_IP := ip }).RIP = ip := by
  simp [afterStep, finishStep, xlatSpec, Operand.write, dataAccess, afterFetches,
    beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

@[simp] theorem afterStep_xlat_external (s : RamState) (length : Nat) (ip : BitVec 64) :
    (afterStep s length fun t => xlatSpec { t with Next_IP := ip }).external = s.external := rfl

theorem Operand.read_afterStep_xlat_rax (s : RamState) (length : Nat) (ip : BitVec 64) :
    (Operand.reg 0 : Operand 64).read
      (afterStep s length fun t => xlatSpec { t with Next_IP := ip }) =
      mergeGPR 8 ((Operand.mem (xlatAddr s) : Operand 8).read s)
        ((Operand.reg 0 : Operand 64).read s) := by
  rw [Operand.read_afterStep]
  simp [xlatSpec, xlatAddr, Operand.write, Operand.read, dataAccess, afterFetches,
    beforeFetch, resetStepFields]

theorem AgreesExcept.afterStep_xlat (s : RamState) (length : Nat) (ip : BitVec 64) :
    AgreesExcept [.reg 0, .rip] s
      (afterStep s length fun t => xlatSpec { t with Next_IP := ip }) := by
  refine (AgreesExcept.of_afterStep s length _ (((AgreesExcept.of_nextIP _ ip).trans
    (AgreesExcept.of_dataAccess _ "load")).trans
    (AgreesExcept.write_reg _ 0 _))).mono ?_
  intro c hc
  simp only [List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> simp

theorem ReadyToStep.afterStep_xlat [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (ip : BitVec 64) :
    ReadyToStep (afterStep s length fun t => xlatSpec { t with Next_IP := ip }) :=
  ReadyToStep.of_agreesExcept h (AgreesExcept.afterStep_xlat s length ip) (by
    rw [afterStep_xlat_external]
    exact h.memory.tables)

theorem xlat_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xD7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32)
    (hr : MemReadable s (xlatAddr s) 1) :
    X86.Machine.step s = some (.next (afterStep s (pre.length + 1) fun t =>
      xlatSpec { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) })) := by
  have hlen' : (pre ++ [0xD7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xD7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_D7_xlat s h _ hrex2 _ pre.length (by omega)
    (by simp) hcode hlow'
  rw [xlat_form _ _ _ (memAlu_dataReady h _) hlock hseg hm64
    (scanContext_address_size _ _ _ hasz) (scanContext_rex_b4 _ _ _) h.cpu.ds
    (hr.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xD7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)

end X86Proofs
