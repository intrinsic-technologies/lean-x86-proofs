import X86Proofs.Instructions.Pop.Generated.R16.Step
import X86Proofs.Instructions.Pop.Generated.R16.Encode
import X86Proofs.Program.ReadWrite.Load
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def popR16Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 ((Operand.mem (stackPtr s) : Operand 16).read s)
        ((Operand.reg dst : Operand 64).read s)⟩,
    ⟨(Operand.reg 4 : Operand 64), stackPtr s + 2⟩]

@[simp] theorem popR16Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) :
    (popR16Effect p len dst s).components = [.reg dst, .reg 4, .rip] := rfl

theorem pop_r16_effect_step [Bindings] (p : BitVec 64) (op : UInt8)
    (hop : PopOpcode op) (hdst : (gprNumber 0 0 (opcodeReg op)) ≠ 4) :
    StepEffect (Pop16Pre p) (codeRange p [0x66, op]) (popR16Effect p 2 (gprNumber 0 0 (opcodeReg op))) := by
  rintro s h hcode hpre
  have hp := hpre.rip
  subst hp
  have hstep := pop_r16_step s h [0x66] (by simpa using scanPrefix_66) (by simp) rfl rfl
    rfl rfl rfl op hop hcode.bytesAt (hcode.low (by simp) (by simp))
    hpre.read
  exact ⟨_, hstep, ReadyToStep.afterStep_pop16 h _ _ _,
    ⟨afterStep_pop16_rip h _ _ _, ⟨Operand.read_afterStep_pop16 _ _ hdst _,
      Operand.read_afterStep_pop16_rsp _ _ hdst _⟩, trivial, AgreesExcept.afterStep_pop16 _ _ _ _⟩⟩

theorem pop_r16_triple_of_bytes [Bindings] (p : BitVec 64) (op : UInt8)
    (hop : PopOpcode op) (hdst : (gprNumber 0 0 (opcodeReg op)) ≠ 4) :
    Triple (Pop16Pre p) (codeRange p [0x66, op]) (Effect.post (popR16Effect p 2 (gprNumber 0 0 (opcodeReg op)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [popR16Effect_components]; simp [Component.Covers]) _)
    (pop_r16_effect_step p op hop hdst)

theorem pop_r16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8) (hrex : RexNoWPrefix rex.toBitVec) (op : UInt8)
    (hop : PopOpcode op) (hdst : (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op)) ≠ 4) :
    StepEffect (Pop16Pre p) (codeRange p [0x66, rex, op]) (popR16Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op))) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hpre
  have hp := hpre.rip
  subst hp
  have hstep := pop_r16_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.rex_w_osz s.DS) op hop hcode.bytesAt (hcode.low (by simp) (by simp))
    hpre.read
  simp only [scanContext_66_rex _ _ hr] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_pop16 h _ _ _,
    ⟨afterStep_pop16_rip h _ _ _, ⟨Operand.read_afterStep_pop16 _ _ hdst _,
      Operand.read_afterStep_pop16_rsp _ _ hdst _⟩, trivial, AgreesExcept.afterStep_pop16 _ _ _ _⟩⟩

theorem pop_r16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8) (hrex : RexNoWPrefix rex.toBitVec) (op : UInt8)
    (hop : PopOpcode op) (hdst : (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op)) ≠ 4) :
    Triple (Pop16Pre p) (codeRange p [0x66, rex, op]) (Effect.post (popR16Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [popR16Effect_components]; simp [Component.Covers]) _)
    (pop_r16_rex_effect_step p rex hrex op hop hdst)

theorem pop_r16_triple [Bindings] (p : BitVec 64) (r : BitVec 4) (hdst : r ≠ 4) :
    Triple (Pop16Pre p) (codeRange p (encodePopR16 r))
      (Effect.post (popR16Effect p (encodePopR16 r).length (r.setWidth 5))) := by
  have hdst5 : r.setWidth 5 ≠ 4 := by
    revert r
    decide
  rcases encodePopR16_spec r with ⟨op, hbytes, hop, hreg⟩ | ⟨rex, op, hbytes, hrex, hop, hreg⟩
  · rw [hbytes, ← hreg]
    exact pop_r16_triple_of_bytes p op hop (hreg ▸ hdst5)
  · rw [hbytes, ← hreg]
    exact pop_r16_rex_triple_of_bytes p rex hrex op hop (hreg ▸ hdst5)

attribute [x86_compose] popR16Effect

@[x86_local] theorem popR16Effect_local {p : BitVec 64} {len : Nat} {r : BitVec 5} :
    Effect.Local (popR16Effect p len r) := by
  effect_local [popR16Effect, stackPtr]

end X86Proofs
