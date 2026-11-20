import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import X86Proofs.Step.PrefixScan
import X86Proofs.Instructions.Idiv.Generated.R.Decode
import X86Proofs.Instructions.Idiv.Generated.R.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem idiv_r64_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7)
    (hcode : BytesAt s s.RIP [rex, 0xF7, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32)
    (hdef : IdivDefined ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s)
        ((Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 64).read s)) :
    let src : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      let r := idivSpec (fun i => oracleBit (oracleSkip t.oracle i))
            ((Operand.reg 2 : Operand 64).read t ++ (Operand.reg 0 : Operand 64).read t)
            (src.read t)
      writePairOutputs t 2 0 r.2.1 r.1 r.2.2 6 (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_F7_idiv s h rex modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdef' : IdivDefined
      ((Operand.reg 2 : Operand 64).read (afterFetches (beforeFetch s) 4) ++
        (Operand.reg 0 : Operand 64).read (afterFetches (beforeFetch s) 4))
      ((Operand.reg (gprNumber (rexContext s.DS rex.toBitVec).rex_b4 (rexContext s.DS rex.toBitVec).rex_b3
        (modrmRm modrm)) : Operand 64).read (afterFetches (beforeFetch s) 4)) := by
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact hdef
  rw [idiv_r_form _ _ _ _ hmode 64 (by decide)
    (hrex.operand_size s.DS) rfl hdef'] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xF7 [modrm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem idiv_r64_ready [Bindings] {s : RamState} (h : ReadyToStep s) (rex modrm : UInt8) :
    let src : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    ReadyToStep (afterStep s 3 fun t =>
      let r := idivSpec (fun i => oracleBit (oracleSkip t.oracle i))
            ((Operand.reg 2 : Operand 64).read t ++ (Operand.reg 0 : Operand 64).read t)
            (src.read t)
      writePairOutputs t 2 0 r.2.1 r.1 r.2.2 6 (BitVec.add s.RIP 3#64)) :=
  ReadyToStep.afterStep_writePairOutputs h 3 _ _ _ _ _ 6 _

theorem idiv_r32_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7)
    (hcode : BytesAt s s.RIP [0xF7, modrm]) (hlow : s.RIP.toNat + 2 ≤ 2^32)
    (hdef : IdivDefined ((Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s)
        ((Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 32).read s)) :
    let src : Operand 32 := .reg (gprNumber 0 0 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 2 fun t =>
      let r := idivSpec (fun i => oracleBit (oracleSkip t.oracle i))
            ((Operand.reg 2 : Operand 32).read t ++ (Operand.reg 0 : Operand 32).read t)
            (src.read t)
      writePairOutputs t 2 0 r.2.1 r.1 r.2.2 6 (BitVec.add s.RIP 2#64))) := by
  have hdecode := decodeLegacy0_run_of_F7_idiv s h modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdef' : IdivDefined
      ((Operand.reg 2 : Operand 32).read (afterFetches (beforeFetch s) 3) ++
        (Operand.reg 0 : Operand 32).read (afterFetches (beforeFetch s) 3))
      ((Operand.reg (gprNumber (legacyContext s.DS).rex_b4 (legacyContext s.DS).rex_b3
        (modrmRm modrm)) : Operand 32).read (afterFetches (beforeFetch s) 3)) := by
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact hdef
  rw [idiv_r_form _ _ _ _ hmode 32 (by decide)
    (legacyContext_operand_size s.DS) rfl hdef'] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xF7 [modrm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem idiv_r32_ready [Bindings] {s : RamState} (h : ReadyToStep s) (modrm : UInt8) :
    let src : Operand 32 := .reg (gprNumber 0 0 (modrmRm modrm))
    ReadyToStep (afterStep s 2 fun t =>
      let r := idivSpec (fun i => oracleBit (oracleSkip t.oracle i))
            ((Operand.reg 2 : Operand 32).read t ++ (Operand.reg 0 : Operand 32).read t)
            (src.read t)
      writePairOutputs t 2 0 r.2.1 r.1 r.2.2 6 (BitVec.add s.RIP 2#64)) :=
  ReadyToStep.afterStep_writePairOutputs h 2 _ _ _ _ _ 6 _

theorem idiv_r32_rex_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7)
    (hcode : BytesAt s s.RIP [rex, 0xF7, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32)
    (hdef : IdivDefined ((Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s)
        ((Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 32).read s)) :
    let src : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      let r := idivSpec (fun i => oracleBit (oracleSkip t.oracle i))
            ((Operand.reg 2 : Operand 32).read t ++ (Operand.reg 0 : Operand 32).read t)
            (src.read t)
      writePairOutputs t 2 0 r.2.1 r.1 r.2.2 6 (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_F7_idiv s h rex modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdef' : IdivDefined
      ((Operand.reg 2 : Operand 32).read (afterFetches (beforeFetch s) 4) ++
        (Operand.reg 0 : Operand 32).read (afterFetches (beforeFetch s) 4))
      ((Operand.reg (gprNumber (rexContext s.DS rex.toBitVec).rex_b4 (rexContext s.DS rex.toBitVec).rex_b3
        (modrmRm modrm)) : Operand 32).read (afterFetches (beforeFetch s) 4)) := by
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact hdef
  rw [idiv_r_form _ _ _ _ hmode 32 (by decide)
    (hrex.operand_size s.DS) rfl hdef'] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xF7 [modrm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem idiv_r32_rex_ready [Bindings] {s : RamState} (h : ReadyToStep s) (rex modrm : UInt8) :
    let src : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    ReadyToStep (afterStep s 3 fun t =>
      let r := idivSpec (fun i => oracleBit (oracleSkip t.oracle i))
            ((Operand.reg 2 : Operand 32).read t ++ (Operand.reg 0 : Operand 32).read t)
            (src.read t)
      writePairOutputs t 2 0 r.2.1 r.1 r.2.2 6 (BitVec.add s.RIP 3#64)) :=
  ReadyToStep.afterStep_writePairOutputs h 3 _ _ _ _ _ 6 _

theorem idiv_r16_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7)
    (hcode : BytesAt s s.RIP [0x66, 0xF7, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32)
    (hdef : IdivDefined ((Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s)
        ((Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 16).read s)) :
    let src : Operand 16 := .reg (gprNumber 0 0 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      let r := idivSpec (fun i => oracleBit (oracleSkip t.oracle i))
            ((Operand.reg 2 : Operand 16).read t ++ (Operand.reg 0 : Operand 16).read t)
            (src.read t)
      writePairOutputs t 2 0 r.2.1 r.1 r.2.2 6 (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_66_F7_idiv s h modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdef' : IdivDefined
      ((Operand.reg 2 : Operand 16).read (afterFetches (beforeFetch s) 4) ++
        (Operand.reg 0 : Operand 16).read (afterFetches (beforeFetch s) 4))
      ((Operand.reg (gprNumber (oszContext s.DS).rex_b4 (oszContext s.DS).rex_b3
        (modrmRm modrm)) : Operand 16).read (afterFetches (beforeFetch s) 4)) := by
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact hdef
  rw [idiv_r16_form _ _ _ _ hmode
    (oszContext_operand_size s.DS) rfl hdef'] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_66_legacy0 s _ h 0xF7 [modrm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem idiv_r16_ready [Bindings] {s : RamState} (h : ReadyToStep s) (modrm : UInt8) :
    let src : Operand 16 := .reg (gprNumber 0 0 (modrmRm modrm))
    ReadyToStep (afterStep s 3 fun t =>
      let r := idivSpec (fun i => oracleBit (oracleSkip t.oracle i))
            ((Operand.reg 2 : Operand 16).read t ++ (Operand.reg 0 : Operand 16).read t)
            (src.read t)
      writePairOutputs t 2 0 r.2.1 r.1 r.2.2 6 (BitVec.add s.RIP 3#64)) :=
  ReadyToStep.afterStep_writePairOutputs h 3 _ _ _ _ _ 6 _

theorem idiv_r16_rex_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7)
    (hcode : BytesAt s s.RIP [0x66, rex, 0xF7, modrm]) (hlow : s.RIP.toNat + 4 ≤ 2^32)
    (hdef : IdivDefined ((Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s)
        ((Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 16).read s)) :
    let src : Operand 16 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      let r := idivSpec (fun i => oracleBit (oracleSkip t.oracle i))
            ((Operand.reg 2 : Operand 16).read t ++ (Operand.reg 0 : Operand 16).read t)
            (src.read t)
      writePairOutputs t 2 0 r.2.1 r.1 r.2.2 6 (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy0_run_of_66_rex_F7_idiv s h rex modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 5) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdef' : IdivDefined
      ((Operand.reg 2 : Operand 16).read (afterFetches (beforeFetch s) 5) ++
        (Operand.reg 0 : Operand 16).read (afterFetches (beforeFetch s) 5))
      ((Operand.reg (gprNumber (oszRexContext s.DS rex.toBitVec).rex_b4 (oszRexContext s.DS rex.toBitVec).rex_b3
        (modrmRm modrm)) : Operand 16).read (afterFetches (beforeFetch s) 5)) := by
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact hdef
  rw [idiv_r16_form _ _ _ _ hmode
    (hrex.operand_size_osz s.DS) rfl hdef'] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_66_rex_legacy0 s _ h rex 0xF7 [modrm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem idiv_r16_rex_ready [Bindings] {s : RamState} (h : ReadyToStep s) (rex modrm : UInt8) :
    let src : Operand 16 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    ReadyToStep (afterStep s 4 fun t =>
      let r := idivSpec (fun i => oracleBit (oracleSkip t.oracle i))
            ((Operand.reg 2 : Operand 16).read t ++ (Operand.reg 0 : Operand 16).read t)
            (src.read t)
      writePairOutputs t 2 0 r.2.1 r.1 r.2.2 6 (BitVec.add s.RIP 4#64)) :=
  ReadyToStep.afterStep_writePairOutputs h 4 _ _ _ _ _ 6 _

end X86Proofs
