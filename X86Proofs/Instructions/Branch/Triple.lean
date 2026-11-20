import X86Proofs.Instructions.Branch.Step
import X86Proofs.Instructions.Nop.Triple
import X86Proofs.Program.Compose

/-!
# Relative branch triples

A relative branch of `len` bytes at `p` with (sign-extended) displacement `off` goes to
`branchTarget p len off = p + len + off` if taken, else to `p + len`. It writes nothing and leaves
the flags alone: its effect only sets RIP.

- `jccEffect p len cc off s`: RIP = the target if `condHolds cc` of `s`'s flags, else `p + len`.
  The effect reads the flags of the start state, so a proof that composes it either knows the
  flags (and simplifies the `if`) or splits on the condition.
- `jmpEffect p len off`: RIP = the target.

Triples, with code `codeRange p bytes`:

| Instruction | Bytes | Length | Triple | Effect |
|---|---|---|---|---|
| `jcc rel8` | `jccOpcode8 cc :: immBytes 8 disp` (`70+cc`) | 2 | `jcc_rel8_triple` | `jccEffect p 2 cc (sext disp)` |
| `jcc rel32` | `0x0F :: jccOpcode32 cc :: immBytes 32 disp` (`0F 80+cc`) | 6 | `jcc_rel32_triple` | `jccEffect p 6 cc (sext disp)` |
| `jmp rel8` | `0xEB :: immBytes 8 disp` | 2 | `jmp_rel8_triple` | `jmpEffect p 2 (sext disp)` |
| `jmp rel32` | `0xE9 :: immBytes 32 disp` | 5 | `jmp_rel32_triple` | `jmpEffect p 5 (sext disp)` |

A taken branch needs its target below 4 GiB (`htarget`). For each `Jcc` width there are also a
taken triple (`_taken_triple`: the condition holds, effect `jmpEffect`) and a not-taken triple
(`_not_taken_triple`: it does not, effect `nopEffect p len`, no `htarget`), for proofs that know
the flags.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- The target of a relative branch of `len` bytes at `p` with displacement `off`. -/
def branchTarget (p : BitVec 64) (len : Nat) (off : BitVec 64) : BitVec 64 :=
  p + BitVec.ofNat 64 len + off

/-- A branch's effect: RIP = `target` if taken, else `nextIP`; nothing else. -/
def branchEffect (taken : Bool) (nextIP target : BitVec 64) : Effect :=
  { rip := if taken then target else nextIP }

/-- The effect of `jcc` (condition `cc`, `len` bytes at `p`, displacement `off`) from the start
state `s`. -/
def jccEffect (p : BitVec 64) (len : Nat) (cc : BitVec 4) (off : BitVec 64) (s : RamState) :
    Effect :=
  branchEffect (condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS)) (p + BitVec.ofNat 64 len)
    (branchTarget p len off)

/-- The effect of `jmp` (`len` bytes at `p`, displacement `off`). -/
def jmpEffect (p : BitVec 64) (len : Nat) (off : BitVec 64) : Effect :=
  { rip := branchTarget p len off }

@[simp] theorem branchEffect_components (taken : Bool) (nextIP target : BitVec 64) :
    (branchEffect taken nextIP target).components = [.rip] := rfl

@[simp] theorem jmpEffect_components (p : BitVec 64) (len : Nat) (off : BitVec 64) :
    (jmpEffect p len off).components = [.rip] := rfl

theorem jmpEffect_avoids (p : BitVec 64) (len : Nat) (off : BitVec 64) (code : CodeMap) :
    (jmpEffect p len off).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem branchEffect_avoids (taken : Bool) (nextIP target : BitVec 64) (code : CodeMap) :
    (branchEffect taken nextIP target).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

/-- The effect of a branch step. -/
theorem branchEffect_holds [Bindings] {s : RamState} (h : ReadyToStep s) (len : Nat)
    (taken : Bool) (nextIP target : BitVec 64) :
    (branchEffect taken nextIP target).Holds s
      (afterStep s len fun t => branchState t taken nextIP target) :=
  ⟨afterStep_branchState_rip h len taken nextIP target, trivial, trivial,
    AgreesExcept.afterStep_branchState s len taken nextIP target⟩

/-- A taken `jcc` has the effect of a `jmp`. -/
theorem jccEffect_taken {p : BitVec 64} {len : Nat} {cc : BitVec 4} {off : BitVec 64}
    {s s' : RamState} (hc : condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = true)
    (h : (jccEffect p len cc off s).Holds s s') : (jmpEffect p len off).Holds s s' := by
  unfold jccEffect at h
  rw [hc] at h
  exact h

/-- A `jcc` not taken has the effect of a NOP. -/
theorem jccEffect_not_taken {p : BitVec 64} {len : Nat} {cc : BitVec 4} {off : BitVec 64}
    {s s' : RamState} (hc : condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = false)
    (h : (jccEffect p len cc off s).Holds s s') : (nopEffect p len).Holds s s' := by
  unfold jccEffect at h
  rw [hc] at h
  exact h

/-- The step behind `jcc_rel8_triple_gen`: from a ready state with the instruction in memory and the
precondition, one `step` reaches a ready state with the effect `jccEffect`. -/
theorem jcc_rel8_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (disp : BitVec 8) :
    StepEffect (fun s => s.RIP = p ∧ (condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = true →
        (branchTarget p 2 (disp.signExtend 64)).toNat < 2^32))
      (codeRange p (jccOpcode8 cc :: immBytes 8 disp))
      (jccEffect p 2 cc (disp.signExtend 64)) := by
  rintro s h hcode ⟨rfl, htarget⟩
  exact ⟨_, jcc_rel8_step s h cc disp hcode.bytesAt (hcode.low (by simp) (by simp)) htarget,
    ReadyToStep.afterStep_branchState h 2 _ _ _, branchEffect_holds h 2 _ _ _⟩

/-- The general `jcc rel8` triple: the target bound only needed when the condition holds. -/
theorem jcc_rel8_triple_gen [Bindings] (p : BitVec 64) (cc : BitVec 4) (disp : BitVec 8) :
    Triple (fun s => s.RIP = p ∧ (condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = true →
        (branchTarget p 2 (disp.signExtend 64)).toNat < 2^32))
      (codeRange p (jccOpcode8 cc :: immBytes 8 disp))
      (Effect.post (jccEffect p 2 cc (disp.signExtend 64))) :=
  Triple.of_effect (fun _ _ => branchEffect_avoids _ _ _ _)
    (jcc_rel8_effect_step p cc disp)

/-- The step behind `jcc_rel32_triple_gen`: from a ready state with the instruction in memory and
the precondition, one `step` reaches a ready state with the effect `jccEffect`. -/
theorem jcc_rel32_effect_step [Bindings] (p : BitVec 64) (cc : BitVec 4) (disp : BitVec 32) :
    StepEffect (fun s => s.RIP = p ∧ (condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = true →
        (branchTarget p 6 (disp.signExtend 64)).toNat < 2^32))
      (codeRange p (0x0F :: jccOpcode32 cc :: immBytes 32 disp))
      (jccEffect p 6 cc (disp.signExtend 64)) := by
  rintro s h hcode ⟨rfl, htarget⟩
  exact ⟨_, jcc_rel32_step s h cc disp hcode.bytesAt (hcode.low (by simp) (by simp)) htarget,
    ReadyToStep.afterStep_branchState h 6 _ _ _, branchEffect_holds h 6 _ _ _⟩

/-- The general `jcc rel32` triple: the target bound only needed when the condition holds. -/
theorem jcc_rel32_triple_gen [Bindings] (p : BitVec 64) (cc : BitVec 4) (disp : BitVec 32) :
    Triple (fun s => s.RIP = p ∧ (condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = true →
        (branchTarget p 6 (disp.signExtend 64)).toNat < 2^32))
      (codeRange p (0x0F :: jccOpcode32 cc :: immBytes 32 disp))
      (Effect.post (jccEffect p 6 cc (disp.signExtend 64))) :=
  Triple.of_effect (fun _ _ => branchEffect_avoids _ _ _ _)
    (jcc_rel32_effect_step p cc disp)

/-- The triple for `jcc rel8` (`70+cc`, displacement `disp`) at `p`: RIP moves to
`p + 2 + sext disp` if `condHolds cc` of the flags, else to `p + 2`. -/
theorem jcc_rel8_triple [Bindings] (p : BitVec 64) (cc : BitVec 4) (disp : BitVec 8)
    (htarget : (branchTarget p 2 (disp.signExtend 64)).toNat < 2^32) :
    Triple (fun s => s.RIP = p) (codeRange p (jccOpcode8 cc :: immBytes 8 disp))
      (Effect.post (jccEffect p 2 cc (disp.signExtend 64))) :=
  (jcc_rel8_triple_gen p cc disp).conseq (fun _ hp => ⟨hp, fun _ => htarget⟩)
    fun _ _ _ h => h

/-- The triple for `jcc rel32` (`0F 80+cc`, displacement `disp`) at `p`: RIP moves to
`p + 6 + sext disp` if `condHolds cc` of the flags, else to `p + 6`. -/
theorem jcc_rel32_triple [Bindings] (p : BitVec 64) (cc : BitVec 4) (disp : BitVec 32)
    (htarget : (branchTarget p 6 (disp.signExtend 64)).toNat < 2^32) :
    Triple (fun s => s.RIP = p) (codeRange p (0x0F :: jccOpcode32 cc :: immBytes 32 disp))
      (Effect.post (jccEffect p 6 cc (disp.signExtend 64))) :=
  (jcc_rel32_triple_gen p cc disp).conseq (fun _ hp => ⟨hp, fun _ => htarget⟩)
    fun _ _ _ h => h

/-- `jcc rel8` when the condition holds: a jump to `p + 2 + sext disp`. -/
theorem jcc_rel8_taken_triple [Bindings] (p : BitVec 64) (cc : BitVec 4) (disp : BitVec 8)
    (htarget : (branchTarget p 2 (disp.signExtend 64)).toNat < 2^32) :
    Triple (fun s => s.RIP = p ∧ condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = true)
      (codeRange p (jccOpcode8 cc :: immBytes 8 disp))
      (Effect.post fun _ => jmpEffect p 2 (disp.signExtend 64)) :=
  (jcc_rel8_triple_gen p cc disp).conseq (fun _ hp => ⟨hp.1, fun _ => htarget⟩)
    fun _ _ hp h => jccEffect_taken hp.2 h

/-- `jcc rel8` when the condition does not hold: only RIP moves, to `p + 2`. -/
theorem jcc_rel8_not_taken_triple [Bindings] (p : BitVec 64) (cc : BitVec 4) (disp : BitVec 8) :
    Triple (fun s => s.RIP = p ∧ condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = false)
      (codeRange p (jccOpcode8 cc :: immBytes 8 disp)) (Effect.post fun _ => nopEffect p 2) :=
  (jcc_rel8_triple_gen p cc disp).conseq
    (fun _ hp => ⟨hp.1, fun hc => absurd (hp.2.symm.trans hc) Bool.false_ne_true⟩)
    fun _ _ hp h => jccEffect_not_taken hp.2 h

/-- `jcc rel32` when the condition holds: a jump to `p + 6 + sext disp`. -/
theorem jcc_rel32_taken_triple [Bindings] (p : BitVec 64) (cc : BitVec 4) (disp : BitVec 32)
    (htarget : (branchTarget p 6 (disp.signExtend 64)).toNat < 2^32) :
    Triple (fun s => s.RIP = p ∧ condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = true)
      (codeRange p (0x0F :: jccOpcode32 cc :: immBytes 32 disp))
      (Effect.post fun _ => jmpEffect p 6 (disp.signExtend 64)) :=
  (jcc_rel32_triple_gen p cc disp).conseq (fun _ hp => ⟨hp.1, fun _ => htarget⟩)
    fun _ _ hp h => jccEffect_taken hp.2 h

/-- `jcc rel32` when the condition does not hold: only RIP moves, to `p + 6`. -/
theorem jcc_rel32_not_taken_triple [Bindings] (p : BitVec 64) (cc : BitVec 4)
    (disp : BitVec 32) :
    Triple (fun s => s.RIP = p ∧ condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS) = false)
      (codeRange p (0x0F :: jccOpcode32 cc :: immBytes 32 disp))
      (Effect.post fun _ => nopEffect p 6) :=
  (jcc_rel32_triple_gen p cc disp).conseq
    (fun _ hp => ⟨hp.1, fun hc => absurd (hp.2.symm.trans hc) Bool.false_ne_true⟩)
    fun _ _ hp h => jccEffect_not_taken hp.2 h

/-- The step behind `jmp_rel8_triple`: from a ready state with the instruction in memory and the
precondition, one `step` reaches a ready state with the effect `jmpEffect`. -/
theorem jmp_rel8_effect_step [Bindings] (p : BitVec 64) (disp : BitVec 8)
    (htarget : (branchTarget p 2 (disp.signExtend 64)).toNat < 2^32) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0xEB :: immBytes 8 disp))
      (fun _ => jmpEffect p 2 (disp.signExtend 64)) := by
  rintro s h hcode rfl
  exact ⟨_, jmp_rel8_step s h disp hcode.bytesAt (hcode.low (by simp) (by simp)) htarget,
    ReadyToStep.afterStep_branchState h 2 _ _ _, branchEffect_holds h 2 true (BitVec.add s.RIP 2#64) _⟩

/-- The triple for `jmp rel8` (`EB`, displacement `disp`) at `p`: RIP moves to
`p + 2 + sext disp`. -/
theorem jmp_rel8_triple [Bindings] (p : BitVec 64) (disp : BitVec 8)
    (htarget : (branchTarget p 2 (disp.signExtend 64)).toNat < 2^32) :
    Triple (fun s => s.RIP = p) (codeRange p (0xEB :: immBytes 8 disp))
      (Effect.post fun _ => jmpEffect p 2 (disp.signExtend 64)) :=
  Triple.of_effect (fun _ _ => jmpEffect_avoids p 2 _ _)
    (jmp_rel8_effect_step p disp htarget)

/-- The step behind `jmp_rel32_triple`: from a ready state with the instruction in memory and the
precondition, one `step` reaches a ready state with the effect `jmpEffect`. -/
theorem jmp_rel32_effect_step [Bindings] (p : BitVec 64) (disp : BitVec 32)
    (htarget : (branchTarget p 5 (disp.signExtend 64)).toNat < 2^32) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0xE9 :: immBytes 32 disp))
      (fun _ => jmpEffect p 5 (disp.signExtend 64)) := by
  rintro s h hcode rfl
  exact ⟨_, jmp_rel32_step s h disp hcode.bytesAt (hcode.low (by simp) (by simp)) htarget,
    ReadyToStep.afterStep_branchState h 5 _ _ _, branchEffect_holds h 5 true (BitVec.add s.RIP 5#64) _⟩

/-- The triple for `jmp rel32` (`E9`, displacement `disp`) at `p`: RIP moves to
`p + 5 + sext disp`. -/
theorem jmp_rel32_triple [Bindings] (p : BitVec 64) (disp : BitVec 32)
    (htarget : (branchTarget p 5 (disp.signExtend 64)).toNat < 2^32) :
    Triple (fun s => s.RIP = p) (codeRange p (0xE9 :: immBytes 32 disp))
      (Effect.post fun _ => jmpEffect p 5 (disp.signExtend 64)) :=
  Triple.of_effect (fun _ _ => jmpEffect_avoids p 5 _ _)
    (jmp_rel32_effect_step p disp htarget)
attribute [x86_compose] branchEffect jmpEffect branchTarget

@[x86_local] theorem branchEffect_local {taken : Bool} {nextIP target : BitVec 64} :
    Effect.Local (fun _ => branchEffect taken nextIP target) := by
  effect_local [branchEffect]

@[x86_local] theorem jmpEffect_local {p : BitVec 64} {len : Nat} {off : BitVec 64} :
    Effect.Local (fun _ => jmpEffect p len off) := by
  effect_local [jmpEffect]

end X86Proofs
