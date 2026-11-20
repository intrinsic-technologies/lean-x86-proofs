
import X86Proofs.Instructions.Bswap.Generated.R.Step
import X86Proofs.Instructions.Bswap.Generated.R.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def bswapR64Effect (p : BitVec 64) (len : Nat) (r : BitVec 5) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg r : Operand 64),
      bswapSpec ((Operand.reg r : Operand 64).read s)⟩] }

@[simp] theorem bswapR64Effect_components (p : BitVec 64) (len : Nat) (r : BitVec 5)
    (s : RamState) :
    (bswapR64Effect p len r s).components = [.reg r, .rip] := rfl

def bswapR32Effect (p : BitVec 64) (len : Nat) (r : BitVec 5) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg r : Operand 64),
      (bswapSpec ((Operand.reg r : Operand 32).read s)).setWidth 64⟩] }

@[simp] theorem bswapR32Effect_components (p : BitVec 64) (len : Nat) (r : BitVec 5)
    (s : RamState) :
    (bswapR32Effect p len r s).components = [.reg r, .rip] := rfl

theorem bswap_r64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (op : UInt8)
    (hop : op ∈ [0xC8, 0xC9, 0xCA, 0xCB, 0xCC, 0xCD, 0xCE, 0xCF]) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x0F, op])
      (bswapR64Effect p 3
        (gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3))) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := bswap_r_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64
    (.inl rfl) (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) op hop
    hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hreg : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (op.toBitVec.extractLsb' 0 3) =
      (gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3)) := rfl
  rw [hreg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self]

theorem bswap_r64_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (op : UInt8)
    (hop : op ∈ [0xC8, 0xC9, 0xCA, 0xCB, 0xCC, 0xCD, 0xCE, 0xCF]) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0x0F, op])
      (Effect.post (bswapR64Effect p 3
        (gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [bswapR64Effect_components]; simp [Component.Covers]) _)
    (bswap_r64_effect_step p rex hrex op hop)

theorem bswap_r32_effect_step [Bindings] (p : BitVec 64) (op : UInt8)
    (hop : op ∈ [0xC8, 0xC9, 0xCA, 0xCB, 0xCC, 0xCD, 0xCE, 0xCF]) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x0F, op])
      (bswapR32Effect p 2
        (gprNumber 0 0 (op.toBitVec.extractLsb' 0 3))) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := bswap_r_step s h [] (by simp) (by simp) 32
    (.inr rfl) (by exact rfl)
    (by rfl) (by rfl) op hop
    hcode.bytesAt hlow
  dsimp only at hstep
  have hreg : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (op.toBitVec.extractLsb' 0 3) =
      (gprNumber 0 0 (op.toBitVec.extractLsb' 0 3)) := rfl
  rw [hreg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32]

theorem bswap_r32_triple_of_bytes [Bindings] (p : BitVec 64) (op : UInt8)
    (hop : op ∈ [0xC8, 0xC9, 0xCA, 0xCB, 0xCC, 0xCD, 0xCE, 0xCF]) :
    Triple (fun s => s.RIP = p) (codeRange p [0x0F, op])
      (Effect.post (bswapR32Effect p 2
        (gprNumber 0 0 (op.toBitVec.extractLsb' 0 3)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [bswapR32Effect_components]; simp [Component.Covers]) _)
    (bswap_r32_effect_step p op hop)

theorem bswap_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (op : UInt8)
    (hop : op ∈ [0xC8, 0xC9, 0xCA, 0xCB, 0xCC, 0xCD, 0xCE, 0xCF]) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x0F, op])
      (bswapR32Effect p 3
        (gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3))) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := bswap_r_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32
    (.inr rfl) (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) op hop
    hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hreg : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (op.toBitVec.extractLsb' 0 3) =
      (gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3)) := rfl
  rw [hreg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32]

theorem bswap_r32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (op : UInt8)
    (hop : op ∈ [0xC8, 0xC9, 0xCA, 0xCB, 0xCC, 0xCD, 0xCE, 0xCF]) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0x0F, op])
      (Effect.post (bswapR32Effect p 3
        (gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [bswapR32Effect_components]; simp [Component.Covers]) _)
    (bswap_r32_rex_effect_step p rex hrex op hop)

theorem bswap_r64_triple [Bindings] (p : BitVec 64) (r : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeBswapR64 r))
      (Effect.post (bswapR64Effect p (encodeBswapR64 r).length (r.setWidth 5))) := by
  obtain ⟨rex, op, hbytes, hrex, hop, hreg⟩ := encodeBswapR64_spec r
  rw [hbytes, ← hreg]
  exact bswap_r64_triple_of_bytes p rex hrex op hop

theorem bswap_r32_triple [Bindings] (p : BitVec 64) (r : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeBswapR32 r))
      (Effect.post (bswapR32Effect p (encodeBswapR32 r).length (r.setWidth 5))) := by
  rcases encodeBswapR32_spec r with ⟨op, hbytes, hop, hreg⟩ |
    ⟨rex, op, hbytes, hrex, hop, hreg⟩
  · rw [hbytes, ← hreg]
    exact bswap_r32_triple_of_bytes p op hop
  · rw [hbytes, ← hreg]
    exact bswap_r32_rex_triple_of_bytes p rex hrex op hop

attribute [x86_compose] bswapR64Effect bswapR32Effect

@[x86_local] theorem bswapR64Effect_local {p : BitVec 64} {len : Nat} {r : BitVec 5} :
    Effect.Local (bswapR64Effect p len r) := by
  effect_local [bswapR64Effect]

@[x86_local] theorem bswapR32Effect_local {p : BitVec 64} {len : Nat} {r : BitVec 5} :
    Effect.Local (bswapR32Effect p len r) := by
  effect_local [bswapR32Effect]

end X86Proofs
