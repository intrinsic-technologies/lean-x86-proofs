import X86Proofs.Instructions.Mov.Generated.R8Imm8.Step
import X86Proofs.Instructions.Mov.Generated.R8Imm8.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movR8Imm8Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8)
    (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 8 imm ((Operand.reg dst : Operand 64).read s)⟩] }

@[simp] theorem movR8Imm8Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (imm : BitVec 8) (s : RamState) :
    (movR8Imm8Effect p len dst imm s).components = [.reg dst, .rip] := rfl

def movR8Imm8NoRexEffect (p : BitVec 64) (len : Nat) (dst : BitVec 3) (imm : BitVec 8)
    (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg (byteRegGpr dst) : Operand 64),
      mergeByteReg dst imm ((Operand.reg (byteRegGpr dst) : Operand 64).read s)⟩] }

@[simp] theorem movR8Imm8NoRexEffect_components (p : BitVec 64) (len : Nat) (dst : BitVec 3)
    (imm : BitVec 8) (s : RamState) :
    (movR8Imm8NoRexEffect p len dst imm s).components =
      [.reg (byteRegGpr dst), .rip] := rfl

theorem mov_r8_imm8_effect_step [Bindings] (p : BitVec 64) (op : UInt8)
    (hop : op ∈ [0xB0, 0xB1, 0xB2, 0xB3]) (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p) (codeRange p (op :: immBytes 8 imm))
      (movR8Imm8Effect p 2 (gprNumber 0 0 (opcodeReg op)) imm) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := mov_r8_imm8_step s h [] (by simp)
    (by simp)
    (by rfl) (by rfl)
    op (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop ⊢
      rcases hop with h | h | h | h <;> simp [h])
    (.inr (gprNumber_zero_lt_four (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl | rfl | rfl <;> decide)))
    imm hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (op.toBitVec.extractLsb' 0 3) =
      (gprNumber 0 0 (opcodeReg op)) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, movSpec]

theorem mov_r8_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (op : UInt8)
    (hop : op ∈ [0xB0, 0xB1, 0xB2, 0xB3]) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (op :: immBytes 8 imm))
      (Effect.post (movR8Imm8Effect p 2 (gprNumber 0 0 (opcodeReg op)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movR8Imm8Effect_components]; simp [Component.Covers]) _)
    (mov_r8_imm8_effect_step p op hop imm)

theorem mov_r8_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (op : UInt8)
    (hop : op ∈ [0xB0, 0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7]) (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: op :: immBytes 8 imm))
      (movR8Imm8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op)) imm) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := mov_r8_imm8_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    op hop (.inl (by rw [scanContext_rex _ _ hr]; rfl))
    imm hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (op.toBitVec.extractLsb' 0 3) =
      (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op)) := rfl
  rw [hdst] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, movSpec]

theorem mov_r8_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hr : RexPrefix rex.toBitVec) (op : UInt8)
    (hop : op ∈ [0xB0, 0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7]) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: op :: immBytes 8 imm))
      (Effect.post (movR8Imm8Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op)) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movR8Imm8Effect_components]; simp [Component.Covers]) _)
    (mov_r8_imm8_rex_effect_step p rex hr op hop imm)

theorem mov_r8_imm8_norex_effect_step [Bindings] (p : BitVec 64) (op : UInt8)
    (hop : op ∈ [0xB0, 0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7]) (imm : BitVec 8) :
    StepEffect (fun s => s.RIP = p) (codeRange p (op :: immBytes 8 imm))
      (movR8Imm8NoRexEffect p 2 (opcodeReg op) imm) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := mov_r8_imm8_gpr8_step s h [] (by simp) (by simp) rfl rfl
    op hop imm hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : Operand.gpr8 (gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (op.toBitVec.extractLsb' 0 3))
      (byteRex (scanContext s.DS (PrefixSegments.ofState s) [])) = Operand.byteReg (opcodeReg op) := rfl
  rw [hdst] at hstep
  simp only [writeResult_byteReg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, Operand.read_afterFetches,
    Operand.read_beforeFetch, movSpec]

theorem mov_r8_imm8_norex_triple_of_bytes [Bindings] (p : BitVec 64) (op : UInt8)
    (hop : op ∈ [0xB0, 0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7]) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (op :: immBytes 8 imm))
      (Effect.post (movR8Imm8NoRexEffect p 2 (opcodeReg op) imm)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movR8Imm8NoRexEffect_components]; simp [Component.Covers]) _)
    (mov_r8_imm8_norex_effect_step p op hop imm)

theorem mov_r8_imm8_norex_triple [Bindings] (p : BitVec 64) (dst : BitVec 3) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeMovR8Imm8NoRex dst imm))
      (Effect.post (movR8Imm8NoRexEffect p 2 dst imm)) := by
  obtain ⟨hop, hdst⟩ := encodeMovR8Imm8NoRex_op dst
  have h := mov_r8_imm8_norex_triple_of_bytes p _ hop imm
  rwa [hdst] at h

theorem mov_r8_imm8_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 8) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeMovR8Imm8 dst imm))
      (Effect.post (movR8Imm8Effect p (encodeMovR8Imm8 dst imm).length (dst.setWidth 5)
        imm)) := by
  rcases encodeMovR8Imm8_spec dst imm with ⟨op, hbytes, hop, hdst⟩ |
    ⟨rex, op, hbytes, hrex, hop, hdst⟩
  · rw [hbytes, ← hdst]
    exact mov_r8_imm8_triple_of_bytes p op hop imm
  · rw [hbytes, ← hdst]
    exact mov_r8_imm8_rex_triple_of_bytes p rex hrex op hop imm

attribute [x86_compose] movR8Imm8Effect

@[x86_local] theorem movR8Imm8Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {imm : BitVec 8} :
    Effect.Local (movR8Imm8Effect p len dst imm) := by
  effect_local [movR8Imm8Effect]

attribute [x86_compose] movR8Imm8NoRexEffect

@[x86_local] theorem movR8Imm8NoRexEffect_local {p : BitVec 64} {len : Nat} {dst : BitVec 3}
    {imm : BitVec 8} :
    Effect.Local (movR8Imm8NoRexEffect p len dst imm) := by
  effect_local [movR8Imm8NoRexEffect]

end X86Proofs
