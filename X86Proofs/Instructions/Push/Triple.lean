import X86Proofs.Program.ReadWrite.Bytes
import X86Proofs.Instructions.Push.Encode
import X86Proofs.Instructions.Push.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

/-!
# PUSH r64 triples

Per encoding, the step with its effect (`push_r64_effect_step`, `push_r64_rex_effect_step`, by
`StepEffect.of_push`, `Program/ReadWrite/Stack.lean`) and a triple for any bytes of that encoding; and one
for the register given by number, so a program proof never decodes REX or opcode bits itself.
`push_r64_step_of_register` and `pushAfter` give the exact state after the push, for runner proofs.

| Instruction | Bytes | Triple (any bytes / by number) | Effect |
|---|---|---|---|
| `push r64` (0–7) | `50+r` | `push_r64_triple_of_bytes` | `pushR64Effect p 1` |
| `push r64` (0–15) | `REX 50+r` | `push_r64_rex_triple_of_bytes` | `pushR64Effect p 2` |
| `push r64` | `encodePushR64 src` | `push_r64_triple` | `pushR64Effect p len` |

Precondition `PushPre p len`: RIP = `p`, the 8 bytes at RSP - 8 below 4 GiB (they may cross a
4 KiB page), present in RAM, none of the page-table entries (`PageTableEntriesApart`), and apart
from the instruction's bytes. Effect: RSP := RSP - 8 and the 8 bytes there := the register (its
value before the push, so `push rsp` pushes the old RSP); flags unchanged.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- The effect of `push src` at `p`, for an encoding of `len` bytes: RIP = `p + len`, RSP set to
RSP - 8, and the 8 bytes at RSP - 8 set to the old value of `src`. -/
def pushR64Effect (p : BitVec 64) (len : Nat) (src : BitVec 5) : RamState → Effect :=
  pushEffect (fun _ => p + BitVec.ofNat 64 len) fun s => (Operand.reg src : Operand 64).read s

@[simp] theorem pushR64Effect_components (p : BitVec 64) (len : Nat) (src : BitVec 5)
    (s : RamState) :
    (pushR64Effect p len src s).components = [.reg 4, .mem (pushAddr s) 8, .rip] :=
  pushEffect_components _ _ s

/--
The step of `push r64` (`50+r` with no prefix) at address `p`, for any opcode `50`–`57`: from a
ready state with the instruction in memory and `PushPre`, one `step` reaches a ready state with the
effect `pushR64Effect` on register `op & 7`.
-/
theorem push_r64_effect_step [Bindings] (p : BitVec 64) (op : UInt8) (hop : PushOpcode op) :
    StepEffect (PushPre p 1) (codeRange p [op])
      (pushR64Effect p 1 (gprNumber 0 0 (opcodeReg op))) := by
  refine StepEffect.of_push _ fun s h hcode hpre => ?_
  have hp := hpre.rip
  subst hp
  exact push_r64_step s h op hop hcode.bytesAt (hcode.low (by simp) (by simp)) hpre.write

/--
The triple for `push r64` (`50+r` with no prefix) at address `p`, for any opcode `50`–`57`: the
effect `pushR64Effect` on register `op & 7`.
-/
theorem push_r64_triple_of_bytes [Bindings] (p : BitVec 64) (op : UInt8) (hop : PushOpcode op) :
    Triple (PushPre p 1) (codeRange p [op])
      (Effect.post (pushR64Effect p 1 (gprNumber 0 0 (opcodeReg op)))) :=
  Triple.of_effect (fun _ hpre => pushEffect_avoids rfl _ _ hpre) (push_r64_effect_step p op hop)

/--
The step of `push r64` (`REX 50+r`) at address `p`, for any REX byte and opcode `50`–`57`: from a
ready state with the instruction in memory and `PushPre`, one `step` reaches a ready state with the
effect `pushR64Effect` on register `op & 7` extended by REX.B.
-/
theorem push_r64_rex_effect_step [Bindings] (p : BitVec 64) (rex op : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hop : PushOpcode op) :
    StepEffect (PushPre p 2) (codeRange p [rex, op])
      (pushR64Effect p 2 (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op))) := by
  refine StepEffect.of_push _ fun s h hcode hpre => ?_
  have hp := hpre.rip
  subst hp
  exact push_r64_rex_step s h rex op hrex hop hcode.bytesAt (hcode.low (by simp) (by simp))
    hpre.write

/--
The triple for `push r64` (`REX 50+r`) at address `p`, for any REX byte and opcode `50`–`57`: the
effect `pushR64Effect` on register `op & 7` extended by REX.B.
-/
theorem push_r64_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex op : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hop : PushOpcode op) :
    Triple (PushPre p 2) (codeRange p [rex, op])
      (Effect.post (pushR64Effect p 2 (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op)))) :=
  Triple.of_effect (fun _ hpre => pushEffect_avoids rfl _ _ hpre)
    (push_r64_rex_effect_step p rex op hrex hop)

/--
The triple for `push src` on the 64-bit register numbered `src` (0–15) at address `p`, in the
encoding `encodePushR64`: the effect `pushR64Effect` on that register, with the length of that
encoding (1 or 2).
-/
theorem push_r64_triple [Bindings] (p : BitVec 64) (src : BitVec 4) :
    Triple (PushPre p (encodePushR64 src).length) (codeRange p (encodePushR64 src))
      (Effect.post (pushR64Effect p (encodePushR64 src).length (src.setWidth 5))) := by
  rcases encodePushR64_spec src with ⟨op, hbytes, hop, hsrc⟩ |
    ⟨rex, op, hbytes, hrex, hop, hsrc⟩
  · rw [hbytes, ← hsrc]
    exact push_r64_triple_of_bytes p op hop
  · rw [hbytes, ← hsrc]
    exact push_r64_rex_triple_of_bytes p rex op hrex hop

/-- Exact state after the shortest encoding of `push src`. -/
def pushAfter (s : RamState) (src : BitVec 4) : RamState :=
  afterStep s (encodePushR64 src).length fun t =>
    pushState { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (encodePushR64 src).length) }
      ((Operand.reg (src.setWidth 5) : Operand 64).read s)

/-- The register-number API with an exact architectural step, for runner proofs. -/
theorem push_r64_step_of_register [Bindings] (s : RamState) (h : ReadyToStep s)
    (src : BitVec 4) (hcode : BytesAt s s.RIP (encodePushR64 src))
    (hlow : s.RIP.toNat + (encodePushR64 src).length ≤ 2^32)
    (hw : MemWritable s (pushAddr s) 8) :
    X86.Machine.step s = some (.next (pushAfter s src)) := by
  unfold pushAfter
  rcases encodePushR64_spec src with ⟨op, hb, hop, hs⟩ | ⟨rex, op, hb, hr, hop, hs⟩
  · simp only [hb, List.length_singleton] at hcode hlow ⊢
    simpa only [hs] using push_r64_step s h op hop hcode hlow hw
  · simp only [hb, List.length_cons, List.length_nil] at hcode hlow ⊢
    simpa only [hs] using push_r64_rex_step s h rex op hr hop hcode hlow hw

/-! ### Examples -/

/-- `push rbp` (`55`). -/
example : encodePushR64 5 = [0x55] := by decide
/-- `push rbx` (`53`). -/
example : encodePushR64 3 = [0x53] := by decide
/-- `push r12` … `push r15` (`41 54` … `41 57`). -/
example : encodePushR64 12 = [0x41, 0x54] ∧ encodePushR64 13 = [0x41, 0x55] ∧
    encodePushR64 14 = [0x41, 0x56] ∧ encodePushR64 15 = [0x41, 0x57] := by decide

/-- `push rbp` at `p`, as a triple on its literal byte. -/
example [Bindings] (p : BitVec 64) :
    Triple (PushPre p 1) (codeRange p [0x55]) (Effect.post (pushR64Effect p 1 5)) :=
  push_r64_triple_of_bytes p 0x55 (by decide)

/-- `push r15` at `p`, as a triple on its literal bytes. -/
example [Bindings] (p : BitVec 64) :
    Triple (PushPre p 2) (codeRange p [0x41, 0x57]) (Effect.post (pushR64Effect p 2 15)) :=
  push_r64_rex_triple_of_bytes p 0x41 0x57 (by unfold RexPrefix; decide) (by decide)

/-- `push r15` by register number: the bytes are `41 57`, the effect pushes R15. -/
example [Bindings] (p : BitVec 64) :
    Triple (PushPre p 2) (codeRange p [0x41, 0x57]) (Effect.post (pushR64Effect p 2 15)) :=
  push_r64_triple p 15

/-- After the push, RSP is the address the word was stored at. -/
@[simp] theorem pushAfter_rsp (s : RamState) (src : BitVec 4) :
    stackPtr (pushAfter s src) = pushAddr s :=
  Operand.read_afterStep_push_rsp s _ _ _

/-- The push changes only RSP, to the old RSP minus 8. -/
@[simp] theorem pushAfter_gpr (s : RamState) (src : BitVec 4) :
    (pushAfter s src).GPR = Vector.set s.GPR 4 (BitVec.sub (stackPtr s) 8) := by
  change Vector.set s.GPR 4 (mergeGPR 64 (BitVec.sub (stackPtr s) 8) s.GPR[4]) = _
  rw [mergeGPR_64]

/-- A push prepends one saved word to an existing stack byte window. -/
theorem Bytes.pushAfter {s : RamState} {len : Nat} {f : Nat → UInt8}
    (h : Bytes s.external (stackPtr s) len f) (src : BitVec 4) (hlen : 8 + len ≤ 2^64) :
    Bytes (pushAfter s src).external (stackPtr (pushAfter s src)) (8 + len)
      (fun i => if i < 8 then storedByte ((Operand.reg (src.setWidth 5) : Operand 64).read s) i
        else f (i - 8)) := by
  let v := (Operand.reg (src.setWidth 5) : Operand 64).read s
  have haddr : pushAddr s + 8#64 = stackPtr s := BitVec.sub_add_cancel _ _
  have ha : RangeApart (pushAddr s) 8 (stackPtr s) len := by
    have h0 := RangeApart.offsets (pushAddr s) (a := 0) (b := 8) (len := 8) (count := len)
      (by decide) hlen (.inl (by decide))
    change RangeApart (pushAddr s + 0#64) 8 (pushAddr s + 8#64) len at h0
    rw [BitVec.add_zero, haddr] at h0
    exact h0
  have ht := h.store_disjoint (pushAddr s) v ha
  have hh := Bytes.store_self s.external (pushAddr s) v (by decide)
  rw [pushAfter_rsp]
  apply hh.append (count := len) (g := f)
  change Bytes (memStore s.external (pushAddr s) v) (pushAddr s + 8#64) len f
  rw [haddr]
  exact ht
attribute [x86_compose] pushR64Effect

@[x86_local] theorem pushR64Effect_local {p : BitVec 64} {len : Nat} {src : BitVec 5} :
    Effect.Local (pushR64Effect p len src) := by
  effect_local [pushR64Effect, pushEffect, pushAddr, stackPtr]

end X86Proofs
