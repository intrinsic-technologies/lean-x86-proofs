import X86Proofs.Instructions.Xchg.Generated.Acc.Step
import X86Proofs.Instructions.Xchg.Generated.Acc.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def xchgR64RaxEffect (p : BitVec 64) (len : Nat) (r : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg r : Operand 64).read s
  let b := (Operand.reg 0 : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64), a⟩,
      ⟨(Operand.reg r : Operand 64), b⟩] }

@[simp] theorem xchgR64RaxEffect_components (p : BitVec 64) (len : Nat) (r : BitVec 5)
    (s : RamState) :
    (xchgR64RaxEffect p len r s).components = [.reg 0, .reg r, .rip] := rfl

def xchgR32EaxEffect (p : BitVec 64) (len : Nat) (r : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg r : Operand 32).read s
  let b := (Operand.reg 0 : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64), a.setWidth 64⟩,
      ⟨(Operand.reg r : Operand 64), b.setWidth 64⟩] }

@[simp] theorem xchgR32EaxEffect_components (p : BitVec 64) (len : Nat) (r : BitVec 5)
    (s : RamState) :
    (xchgR32EaxEffect p len r s).components = [.reg 0, .reg r, .rip] := rfl

def xchgR16AxEffect (p : BitVec 64) (len : Nat) (r : BitVec 5) (s : RamState) : Effect :=
  let a := (Operand.reg r : Operand 16).read s
  let b := (Operand.reg 0 : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64), mergeGPR 16 a ((Operand.reg 0 : Operand 64).read s)⟩,
      ⟨(Operand.reg r : Operand 64), mergeGPR 16 b ((Operand.reg r : Operand 64).read s)⟩] }

@[simp] theorem xchgR16AxEffect_components (p : BitVec 64) (len : Nat) (r : BitVec 5)
    (s : RamState) :
    (xchgR16AxEffect p len r s).components = [.reg 0, .reg r, .rip] := rfl

theorem xchg_r64_rax_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (op : UInt8)
    (hop : op ∈ [0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97])
    (h90 : op = 0x90 → rexB rex.toBitVec = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, op])
      (xchgR64RaxEffect p 2
        (gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3))) := by
  have hr := hrex.rexPrefix
  have hne : (0 : BitVec 5) ≠ (gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3)) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h90 rfl]; decide
    all_goals generalize rexB rex.toBitVec = b; revert b; decide
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := xchg_r_rax_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) op
    hop (fun h0 => ⟨(by rw [scanContext_rex _ _ hr]; exact h90 h0),
      (by rw [scanContext_rex _ _ hr]; rfl)⟩)
    hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hreg : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (op.toBitVec.extractLsb' 0 3) =
      (gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3)) := rfl
  rw [hreg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResultPair h _ _ _ _ _ _,
    ⟨afterStep_writeResultPair_rip h _ _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResultPair s _ _ _ _ _ _⟩⟩
  show Operand.read _ _ = _ ∧ Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_afterStep, Operand.read_writeResultPair_fst _ hne,
    Operand.read_writeResultPair_snd _ hne]
  simp only [xchgSpec, Operand.read_afterFetches, Operand.read_beforeFetch, mergeGPR_64, and_self]

theorem xchg_r64_rax_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (op : UInt8)
    (hop : op ∈ [0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97])
    (h90 : op = 0x90 → rexB rex.toBitVec = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, op])
      (Effect.post (xchgR64RaxEffect p 2
        (gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [xchgR64RaxEffect_components]; simp [Component.Covers]) _)
    (xchg_r64_rax_effect_step p rex hrex op hop h90)

theorem xchg_r32_eax_effect_step [Bindings] (p : BitVec 64) (op : UInt8)
    (hop : op ∈ [0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97]) :
    StepEffect (fun s => s.RIP = p) (codeRange p [op])
      (xchgR32EaxEffect p 1
        (gprNumber 0 0 (op.toBitVec.extractLsb' 0 3))) := by
  have hne : (0 : BitVec 5) ≠ (gprNumber 0 0 (op.toBitVec.extractLsb' 0 3)) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := xchg_r_rax_step s h [] (by simp) (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl) op
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hop ⊢
        rcases hop with h | h | h | h | h | h | h <;> simp [h])
    (fun h0 => absurd h0 (by rintro rfl; revert hop; decide))
    hcode.bytesAt hlow
  dsimp only at hstep
  have hreg : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (op.toBitVec.extractLsb' 0 3) =
      (gprNumber 0 0 (op.toBitVec.extractLsb' 0 3)) := rfl
  rw [hreg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResultPair h _ _ _ _ _ _,
    ⟨afterStep_writeResultPair_rip h _ _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResultPair s _ _ _ _ _ _⟩⟩
  show Operand.read _ _ = _ ∧ Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_afterStep, Operand.read_writeResultPair_fst _ hne,
    Operand.read_writeResultPair_snd _ hne]
  simp only [xchgSpec, Operand.read_afterFetches, Operand.read_beforeFetch, mergeGPR_32, and_self]

theorem xchg_r32_eax_triple_of_bytes [Bindings] (p : BitVec 64) (op : UInt8)
    (hop : op ∈ [0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97]) :
    Triple (fun s => s.RIP = p) (codeRange p [op])
      (Effect.post (xchgR32EaxEffect p 1
        (gprNumber 0 0 (op.toBitVec.extractLsb' 0 3)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [xchgR32EaxEffect_components]; simp [Component.Covers]) _)
    (xchg_r32_eax_effect_step p op hop)

theorem xchg_r32_eax_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (op : UInt8)
    (hop : op ∈ [0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97])
    (h90 : op = 0x90 → rexB rex.toBitVec = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, op])
      (xchgR32EaxEffect p 2
        (gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3))) := by
  have hr := hrex.rexPrefix
  have hne : (0 : BitVec 5) ≠ (gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3)) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h90 rfl]; decide
    all_goals generalize rexB rex.toBitVec = b; revert b; decide
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := xchg_r_rax_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) op
    hop (fun h0 => ⟨(by rw [scanContext_rex _ _ hr]; exact h90 h0),
      (by rw [scanContext_rex _ _ hr]; rfl)⟩)
    hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hreg : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (op.toBitVec.extractLsb' 0 3) =
      (gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3)) := rfl
  rw [hreg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResultPair h _ _ _ _ _ _,
    ⟨afterStep_writeResultPair_rip h _ _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResultPair s _ _ _ _ _ _⟩⟩
  show Operand.read _ _ = _ ∧ Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_afterStep, Operand.read_writeResultPair_fst _ hne,
    Operand.read_writeResultPair_snd _ hne]
  simp only [xchgSpec, Operand.read_afterFetches, Operand.read_beforeFetch, mergeGPR_32, and_self]

theorem xchg_r32_eax_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (op : UInt8)
    (hop : op ∈ [0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97])
    (h90 : op = 0x90 → rexB rex.toBitVec = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, op])
      (Effect.post (xchgR32EaxEffect p 2
        (gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [xchgR32EaxEffect_components]; simp [Component.Covers]) _)
    (xchg_r32_eax_rex_effect_step p rex hrex op hop h90)

theorem xchg_r16_ax_effect_step [Bindings] (p : BitVec 64) (op : UInt8)
    (hop : op ∈ [0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97]) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, op])
      (xchgR16AxEffect p 2
        (gprNumber 0 0 (op.toBitVec.extractLsb' 0 3))) := by
  have hne : (0 : BitVec 5) ≠ (gprNumber 0 0 (op.toBitVec.extractLsb' 0 3)) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := xchg_r16_ax_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    (by exact rfl)
    (by rfl) (by rfl) op
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hop ⊢
        rcases hop with h | h | h | h | h | h | h <;> simp [h])
    (fun h0 => absurd h0 (by rintro rfl; revert hop; decide))
    hcode.bytesAt hlow
  dsimp only at hstep
  have hreg : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b3 (op.toBitVec.extractLsb' 0 3) =
      (gprNumber 0 0 (op.toBitVec.extractLsb' 0 3)) := rfl
  rw [hreg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResultPair h _ _ _ _ _ _,
    ⟨afterStep_writeResultPair_rip h _ _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResultPair s _ _ _ _ _ _⟩⟩
  show Operand.read _ _ = _ ∧ Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_afterStep, Operand.read_writeResultPair_fst _ hne,
    Operand.read_writeResultPair_snd _ hne]
  simp only [xchgSpec, Operand.read_afterFetches, Operand.read_beforeFetch, and_self]

theorem xchg_r16_ax_triple_of_bytes [Bindings] (p : BitVec 64) (op : UInt8)
    (hop : op ∈ [0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97]) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, op])
      (Effect.post (xchgR16AxEffect p 2
        (gprNumber 0 0 (op.toBitVec.extractLsb' 0 3)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [xchgR16AxEffect_components]; simp [Component.Covers]) _)
    (xchg_r16_ax_effect_step p op hop)

theorem xchg_r16_ax_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (op : UInt8)
    (hop : op ∈ [0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97])
    (h90 : op = 0x90 → rexB rex.toBitVec = 1) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x66, rex, op])
      (xchgR16AxEffect p 3
        (gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3))) := by
  have hr := hrex.rexPrefix
  have hne : (0 : BitVec 5) ≠ (gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3)) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h90 rfl]; decide
    all_goals generalize rexB rex.toBitVec = b; revert b; decide
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := xchg_r16_ax_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl) op
    hop (fun h0 => ⟨(by rw [scanContext_66_rex _ _ hr]; exact h90 h0),
      (by rw [scanContext_66_rex _ _ hr]; rfl)⟩)
    hcode.bytesAt hlow
  simp only [scanContext_66_rex _ _ hr] at hstep
  have hreg : gprNumber (oszRexContext s.DS rex.toBitVec).rex_b4
      (oszRexContext s.DS rex.toBitVec).rex_b3 (op.toBitVec.extractLsb' 0 3) =
      (gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3)) := rfl
  rw [hreg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResultPair h _ _ _ _ _ _,
    ⟨afterStep_writeResultPair_rip h _ _ _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResultPair s _ _ _ _ _ _⟩⟩
  show Operand.read _ _ = _ ∧ Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_afterStep, Operand.read_writeResultPair_fst _ hne,
    Operand.read_writeResultPair_snd _ hne]
  simp only [xchgSpec, Operand.read_afterFetches, Operand.read_beforeFetch, and_self]

theorem xchg_r16_ax_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (op : UInt8)
    (hop : op ∈ [0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97])
    (h90 : op = 0x90 → rexB rex.toBitVec = 1) :
    Triple (fun s => s.RIP = p) (codeRange p [0x66, rex, op])
      (Effect.post (xchgR16AxEffect p 3
        (gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [xchgR16AxEffect_components]; simp [Component.Covers]) _)
    (xchg_r16_ax_rex_effect_step p rex hrex op hop h90)

theorem xchg_r64_rax_triple [Bindings] (p : BitVec 64) (r : BitVec 4) (hr : r ≠ 0) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeXchgR64Rax r))
      (Effect.post (xchgR64RaxEffect p (encodeXchgR64Rax r).length (r.setWidth 5))) := by
  obtain ⟨rex, op, hbytes, hrex, hop, h90, hreg⟩ := encodeXchgR64Rax_spec r hr
  rw [hbytes, ← hreg]
  exact xchg_r64_rax_triple_of_bytes p rex hrex op hop h90

theorem xchg_r32_eax_triple [Bindings] (p : BitVec 64) (r : BitVec 4) (hr : r ≠ 0) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeXchgR32Eax r))
      (Effect.post (xchgR32EaxEffect p (encodeXchgR32Eax r).length (r.setWidth 5))) := by
  rcases encodeXchgR32Eax_spec r hr with ⟨op, hbytes, hop, hreg⟩ |
    ⟨rex, op, hbytes, hrex, hop, h90, hreg⟩
  · rw [hbytes, ← hreg]
    exact xchg_r32_eax_triple_of_bytes p op hop
  · rw [hbytes, ← hreg]
    exact xchg_r32_eax_rex_triple_of_bytes p rex hrex op hop h90

theorem xchg_r16_ax_triple [Bindings] (p : BitVec 64) (r : BitVec 4) (hr : r ≠ 0) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeXchgR16Ax r))
      (Effect.post (xchgR16AxEffect p (encodeXchgR16Ax r).length (r.setWidth 5))) := by
  rcases encodeXchgR16Ax_spec r hr with ⟨op, hbytes, hop, hreg⟩ |
    ⟨rex, op, hbytes, hrex, hop, h90, hreg⟩
  · rw [hbytes, ← hreg]
    exact xchg_r16_ax_triple_of_bytes p op hop
  · rw [hbytes, ← hreg]
    exact xchg_r16_ax_rex_triple_of_bytes p rex hrex op hop h90

attribute [x86_compose] xchgR64RaxEffect xchgR32EaxEffect xchgR16AxEffect

@[x86_local] theorem xchgR64RaxEffect_local {p : BitVec 64} {len : Nat} {r : BitVec 5} :
    Effect.Local (xchgR64RaxEffect p len r) := by
  effect_local [xchgR64RaxEffect]

@[x86_local] theorem xchgR32EaxEffect_local {p : BitVec 64} {len : Nat} {r : BitVec 5} :
    Effect.Local (xchgR32EaxEffect p len r) := by
  effect_local [xchgR32EaxEffect]

@[x86_local] theorem xchgR16AxEffect_local {p : BitVec 64} {len : Nat} {r : BitVec 5} :
    Effect.Local (xchgR16AxEffect p len r) := by
  effect_local [xchgR16AxEffect]

end X86Proofs
