import X86Proofs.Instructions.Pop.Step
import X86Proofs.Instructions.Pop.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

/-!
# POP r64 triples

Per encoding, the step with its effect (`pop_r64_effect_step`, `pop_r64_rex_effect_step`, by
`StepEffect.of_pop`) and a triple for any bytes of that encoding; and one for the register given
by number, so a program proof never decodes REX or opcode bits itself.

| Instruction | Bytes | Triple (any bytes / by number) | Effect |
|---|---|---|---|
| `pop r64` (0–7) | `58+r` | `pop_r64_triple_of_bytes` | `popR64Effect p 1` |
| `pop r64` (0–15) | `REX 58+r` | `pop_r64_rex_triple_of_bytes` | `popR64Effect p 2` |
| `pop r64` | `encodePopR64 dst` | `pop_r64_triple` | `popR64Effect p len` |

Precondition `PopPre p`: RIP = `p`, the 8 bytes at RSP below 4 GiB and present in RAM (they may
cross a 4 KiB page). Effect: the register := those 8 bytes, RSP := RSP + 8; flags and memory
unchanged. The destination must not be RSP (`pop rsp` sets RSP to the value read
instead), so each triple asks `dst ≠ 4`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- The effect of `pop dst` at `p`, for an encoding of `len` bytes: RIP = `p + len`, `dst` set to
the 8 bytes at RSP and RSP to RSP + 8 (for `dst` ≠ RSP). -/
def popR64Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.reg dst : Operand 64), (Operand.mem (stackPtr s) : Operand 64).read s⟩,
    ⟨(Operand.reg 4 : Operand 64), stackPtr s + 8⟩]

@[simp] theorem popR64Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (popR64Effect p len dst s).components = [.reg dst, .reg 4, .rip] := rfl

/-- A pop writes no memory, so it avoids any code. -/
theorem popR64Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState)
    (code : CodeMap) : (popR64Effect p len dst s).Avoids code :=
  Effect.Avoids.of_noMem (by rw [popR64Effect_components]; simp [Component.Covers]) code

/--
The step of a pop form at `p` into `dst` ≠ RSP with its effect, from its step theorem. If from
every ready state with the instruction `bytes` at `p` and `PopPre`, one `step` runs the form,
ending in a pop into `dst` with `Next_IP` = `p + len`, then that step reaches a ready state with the
effect `popR64Effect`.
-/
theorem StepEffect.of_pop [Bindings] {p : BitVec 64} {bytes : List UInt8} {len : Nat}
    {dst : BitVec 5} (hdst : dst ≠ 4)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → PopPre p s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        popState { t with Next_IP := BitVec.add p (BitVec.ofNat 64 len) } dst))) :
    StepEffect (PopPre p) (codeRange p bytes) (popR64Effect p len dst) := by
  intro s h hcode hpre
  exact ⟨_, hstep s h hcode hpre, ReadyToStep.afterStep_pop h _ _ _,
    ⟨afterStep_pop_rip h _ _ _, ⟨Operand.read_afterStep_pop _ _ _ _,
      Operand.read_afterStep_pop_rsp _ _ hdst _⟩, trivial, AgreesExcept.afterStep_pop _ _ _ _⟩⟩

/--
The triple of a pop form at `p` into `dst` ≠ RSP, from its step theorem (as `StepEffect.of_pop`):
the effect `popR64Effect`.
-/
theorem Triple.of_pop [Bindings] {p : BitVec 64} {bytes : List UInt8} {len : Nat} {dst : BitVec 5}
    (hdst : dst ≠ 4)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → PopPre p s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        popState { t with Next_IP := BitVec.add p (BitVec.ofNat 64 len) } dst))) :
    Triple (PopPre p) (codeRange p bytes) (Effect.post (popR64Effect p len dst)) :=
  Triple.of_effect (fun s _ => popR64Effect_avoids p len dst s _) (StepEffect.of_pop hdst hstep)

/--
The step of `pop r64` (`58+r` with no prefix) at address `p`, for any opcode `58`–`5F` but `5C`
(`pop rsp`): from a ready state with the instruction in memory and `PopPre`, one `step` reaches a
ready state with the effect `popR64Effect` on register `op & 7`.
-/
theorem pop_r64_effect_step [Bindings] (p : BitVec 64) (op : UInt8) (hop : PopOpcode op)
    (hdst : gprNumber 0 0 (opcodeReg op) ≠ 4) :
    StepEffect (PopPre p) (codeRange p [op])
      (popR64Effect p 1 (gprNumber 0 0 (opcodeReg op))) := by
  refine StepEffect.of_pop hdst fun s h hcode hpre => ?_
  have hp := hpre.rip
  subst hp
  exact pop_r64_step s h op hop hcode.bytesAt (hcode.low (by simp) (by simp)) hpre.read

/--
The triple for `pop r64` (`58+r` with no prefix) at address `p`, for any opcode `58`–`5F` but `5C`
(`pop rsp`): the effect `popR64Effect` on register `op & 7`.
-/
theorem pop_r64_triple_of_bytes [Bindings] (p : BitVec 64) (op : UInt8) (hop : PopOpcode op)
    (hdst : gprNumber 0 0 (opcodeReg op) ≠ 4) :
    Triple (PopPre p) (codeRange p [op])
      (Effect.post (popR64Effect p 1 (gprNumber 0 0 (opcodeReg op)))) :=
  Triple.of_effect (fun s _ => popR64Effect_avoids p _ _ s _) (pop_r64_effect_step p op hop hdst)

/--
The step of `pop r64` (`REX 58+r`) at address `p`, for any REX byte and opcode `58`–`5F` whose
register (`op & 7` extended by REX.B) is not RSP: from a ready state with the instruction in memory
and `PopPre`, one `step` reaches a ready state with the effect `popR64Effect` on that register.
-/
theorem pop_r64_rex_effect_step [Bindings] (p : BitVec 64) (rex op : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hop : PopOpcode op)
    (hdst : gprNumber 0 (rexB rex.toBitVec) (opcodeReg op) ≠ 4) :
    StepEffect (PopPre p) (codeRange p [rex, op])
      (popR64Effect p 2 (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op))) := by
  refine StepEffect.of_pop hdst fun s h hcode hpre => ?_
  have hp := hpre.rip
  subst hp
  exact pop_r64_rex_step s h rex op hrex hop hcode.bytesAt (hcode.low (by simp) (by simp))
    hpre.read

/--
The triple for `pop r64` (`REX 58+r`) at address `p`, for any REX byte and opcode `58`–`5F` whose
register (`op & 7` extended by REX.B) is not RSP: the effect `popR64Effect` on that register.
-/
theorem pop_r64_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex op : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hop : PopOpcode op)
    (hdst : gprNumber 0 (rexB rex.toBitVec) (opcodeReg op) ≠ 4) :
    Triple (PopPre p) (codeRange p [rex, op])
      (Effect.post (popR64Effect p 2 (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op)))) :=
  Triple.of_effect (fun s _ => popR64Effect_avoids p _ _ s _)
    (pop_r64_rex_effect_step p rex op hrex hop hdst)

/--
The triple for `pop dst` on the 64-bit register numbered `dst` (0–15, not RSP) at address `p`, in
the encoding `encodePopR64`: the effect `popR64Effect` on that register, with the length of that
encoding (1 or 2).
-/
theorem pop_r64_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (hdst : dst ≠ 4) :
    Triple (PopPre p) (codeRange p (encodePopR64 dst))
      (Effect.post (popR64Effect p (encodePopR64 dst).length (dst.setWidth 5))) := by
  have hdst5 : dst.setWidth 5 ≠ 4 := by
    revert dst
    decide
  rcases encodePopR64_spec dst with ⟨op, hbytes, hop, hreg⟩ |
    ⟨rex, op, hbytes, hrex, hop, hreg⟩
  · rw [hbytes, ← hreg]
    exact pop_r64_triple_of_bytes p op hop (hreg ▸ hdst5)
  · rw [hbytes, ← hreg]
    exact pop_r64_rex_triple_of_bytes p rex op hrex hop (hreg ▸ hdst5)

/-- The state after popping into a register, with the canonical opcode encoding. -/
def popAfter (s : RamState) (dst : BitVec 4) : RamState :=
  afterStep s (encodePopR64 dst).length fun t =>
    popState { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (encodePopR64 dst).length) }
      (dst.setWidth 5)

/-- Register-number API for an exact POP step. -/
theorem pop_r64_step_of_register [Bindings] (s : RamState) (h : ReadyToStep s)
    (dst : BitVec 4) (hcode : BytesAt s s.RIP (encodePopR64 dst))
    (hlow : s.RIP.toNat + (encodePopR64 dst).length ≤ 2^32)
    (hr : MemReadable s (stackPtr s) 8) :
    X86.Machine.step s = some (.next (popAfter s dst)) := by
  unfold popAfter
  rcases encodePopR64_spec dst with ⟨op, hb, hop, hs⟩ | ⟨rex, op, hb, hre, hop, hs⟩
  · simp only [hb, List.length_singleton] at hcode hlow ⊢
    simpa only [hs] using pop_r64_step s h op hop hcode hlow hr
  · simp only [hb, List.length_cons, List.length_nil] at hcode hlow ⊢
    simpa only [hs] using pop_r64_rex_step s h rex op hre hop hcode hlow hr

/-- After popping into a register other than RSP, RSP is the old RSP plus 8. -/
@[simp] theorem popAfter_rsp (s : RamState) (dst : BitVec 4) (hdst : dst ≠ 4) :
    stackPtr (popAfter s dst) = stackPtr s + 8 := by
  apply Operand.read_afterStep_pop_rsp
  revert dst
  decide

/-- A pop leaves memory unchanged. -/
@[simp] theorem popAfter_external (s : RamState) (dst : BitVec 4) :
    (popAfter s dst).external = s.external := rfl

/-- The popped register holds the word that was on top of the stack. -/
theorem popAfter_value (s : RamState) (dst : BitVec 4) :
    (Operand.reg (dst.setWidth 5) : Operand 64).read (popAfter s dst) =
      (Operand.mem (stackPtr s) : Operand 64).read s :=
  Operand.read_afterStep_pop s _ _ _

/-! ### Examples -/

/-- `pop rbx` (`5B`), `pop rbp` (`5D`). -/
example : encodePopR64 3 = [0x5B] ∧ encodePopR64 5 = [0x5D] := by decide
/-- `pop r12` … `pop r15` (`41 5C` … `41 5F`). -/
example : encodePopR64 12 = [0x41, 0x5C] ∧ encodePopR64 13 = [0x41, 0x5D] ∧
    encodePopR64 14 = [0x41, 0x5E] ∧ encodePopR64 15 = [0x41, 0x5F] := by decide

/-- `pop rbx` at `p`, as a triple on its literal byte. -/
example [Bindings] (p : BitVec 64) :
    Triple (PopPre p) (codeRange p [0x5B]) (Effect.post (popR64Effect p 1 3)) :=
  pop_r64_triple_of_bytes p 0x5B (by decide) (by decide)

/-- `pop rbp` at `p`, as a triple on its literal byte. -/
example [Bindings] (p : BitVec 64) :
    Triple (PopPre p) (codeRange p [0x5D]) (Effect.post (popR64Effect p 1 5)) :=
  pop_r64_triple_of_bytes p 0x5D (by decide) (by decide)

/-- `pop r12` at `p` (`41 5C`: opcode `5C` with REX.B is R12, not RSP), as a triple on
its literal bytes. -/
example [Bindings] (p : BitVec 64) :
    Triple (PopPre p) (codeRange p [0x41, 0x5C]) (Effect.post (popR64Effect p 2 12)) :=
  pop_r64_rex_triple_of_bytes p 0x41 0x5C (by unfold RexPrefix; decide) (by decide) (by decide)

/-- `pop r15` by register number: the bytes are `41 5F`, the effect pops into R15. -/
example [Bindings] (p : BitVec 64) :
    Triple (PopPre p) (codeRange p [0x41, 0x5F]) (Effect.post (popR64Effect p 2 15)) :=
  pop_r64_triple p 15 (by decide)
attribute [x86_compose] popR64Effect

@[x86_local] theorem popR64Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5} :
    Effect.Local (popR64Effect p len dst) := by
  effect_local [popR64Effect, stackPtr]

end X86Proofs
