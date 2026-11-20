import X86Proofs.Instructions.Mov.Generated.R16Imm16.Step
import X86Proofs.Instructions.Mov.Generated.R16Imm16.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movR16Imm16Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16)
    (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 imm ((Operand.reg dst : Operand 64).read s)⟩] }

@[simp] theorem movR16Imm16Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (imm : BitVec 16) (s : RamState) :
    (movR16Imm16Effect p len dst imm s).components = [.reg dst, .rip] := rfl

theorem mov_r16_imm16_effect_step [Bindings] (p : BitVec 64) (op : UInt8)
    (hop : MovImmOpcode op) (imm : BitVec 16) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x66 :: op :: immBytes 16 imm))
      (movR16Imm16Effect p 4 (gprNumber 0 0 (opcodeReg op)) imm) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := mov_r16_imm16_step s h [0x66] (by simpa using scanPrefix_66)
    (by simp)
    (by exact rfl)
    (by rfl) (by rfl)
    op hop
    imm hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b3 (op.toBitVec.extractLsb' 0 3) =
      (gprNumber 0 0 (opcodeReg op)) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, movSpec]

theorem mov_r16_imm16_triple_of_bytes [Bindings] (p : BitVec 64) (op : UInt8)
    (hop : MovImmOpcode op) (imm : BitVec 16) :
    Triple (fun s => s.RIP = p) (codeRange p (0x66 :: op :: immBytes 16 imm))
      (Effect.post (movR16Imm16Effect p 4 (gprNumber 0 0 (opcodeReg op)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movR16Imm16Effect_components]; simp [Component.Covers]) _)
    (mov_r16_imm16_effect_step p op hop imm)

theorem mov_r16_imm16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (op : UInt8)
    (hop : MovImmOpcode op) (imm : BitVec 16) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x66 :: rex :: op :: immBytes 16 imm))
      (movR16Imm16Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op)) imm) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := mov_r16_imm16_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix])
    (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    op hop
    imm hcode.bytesAt hlow
  simp only [scanContext_66_rex _ _ hr] at hstep
  have hdst : gprNumber (oszRexContext s.DS rex.toBitVec).rex_b4
      (oszRexContext s.DS rex.toBitVec).rex_b3 (op.toBitVec.extractLsb' 0 3) =
      (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op)) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, movSpec]

theorem mov_r16_imm16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (op : UInt8)
    (hop : MovImmOpcode op) (imm : BitVec 16) :
    Triple (fun s => s.RIP = p) (codeRange p (0x66 :: rex :: op :: immBytes 16 imm))
      (Effect.post (movR16Imm16Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movR16Imm16Effect_components]; simp [Component.Covers]) _)
    (mov_r16_imm16_rex_effect_step p rex hrex op hop imm)

theorem mov_r16_imm16_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 16) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeMovR16Imm16 dst imm))
      (Effect.post (movR16Imm16Effect p (encodeMovR16Imm16 dst imm).length (dst.setWidth 5)
        imm)) := by
  rcases encodeMovR16Imm16_spec dst imm with ⟨op, hbytes, hop, hdst⟩ |
    ⟨rex, op, hbytes, hrex, hop, hdst⟩
  · rw [hbytes, ← hdst]
    exact mov_r16_imm16_triple_of_bytes p op hop imm
  · rw [hbytes, ← hdst]
    exact mov_r16_imm16_rex_triple_of_bytes p rex hrex op hop imm

attribute [x86_compose] movR16Imm16Effect

@[x86_local] theorem movR16Imm16Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {imm : BitVec 16} :
    Effect.Local (movR16Imm16Effect p len dst imm) := by
  effect_local [movR16Imm16Effect]

end X86Proofs
