import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Call.Decode
import X86Proofs.Instructions.Branch.Step
import X86Proofs.Step.MemOperand

/-!
# Layer 3: CALL and RET step theorems

| Instruction | Bytes | Step theorem | Result (`afterStep s L fun t => …`) |
|---|---|---|---|
| `call rel32` | `E8 cd` | `call_rel32_step` | `callState (callFrom false t (RIP+5)) (RIP+5) (RIP+5+sext disp)` |
| `call r64` | `pre FF /2` (`mod = 3`) | `call_r64_step` | `callState (callFrom false t (RIP+L)) (RIP+L) rm` |
| `call [mem]` | `pre FF /2` (`mod ≠ 3`) | `call_m64_step` | `callState (callFrom true t (RIP+L)) (RIP+L) [ptr]` |
| `call fs:[mem]` | `pre FF /2` (`mod ≠ 3`), any segment prefix | `call_m64_seg_step` | as `call_m64_step`, the pointer at `segAddr ctx (am.addrAt s L)` |
| `call [mem]`, address size 32 | `pre FF /2` (`mod ≠ 3`), `67` in `pre` | `call_m64_a32_step` | as `call_m64_seg_step`, the pointer at `segAddr ctx (am.addrAt32 s L)` |
| `ret` | `C3` | `ret_step` | `retState (withNextIP t (RIP+1))` |

`callFrom load t nextIP` is the state the push starts from (`Next_IP` set; for `call [mem]` after
the pointer read's bookkeeping). The `FF /2` theorems take any prefix list the prefix scan covers
(as the memory ALU forms do); the triples use none or one REX byte.

What a step preserves: `afterStep_call_rip` (RIP = target), `Operand.read_afterStep_call_rsp`
(RSP = RSP - 8), `Operand.read_afterStep_call_mem` (the 8 bytes at the old RSP - 8 = the return
address), `AgreesExcept.afterStep_call` (`[.reg 4, .mem (RSP - 8) 8, .rip]`),
`ReadyToStep.afterStep_call`; `afterStep_ret_rip` (RIP = `stackTop s`),
`Operand.read_afterStep_ret_rsp` (RSP + 8), `AgreesExcept.afterStep_ret` (`[.reg 4, .rip]`),
`ReadyToStep.afterStep_ret`; for `RET imm16` (`retImmState`): `afterStep_retImm_rip`,
`Operand.read_afterStep_retImm_rsp` (RSP + 8 + `imm`), `AgreesExcept.afterStep_retImm`,
`ReadyToStep.afterStep_retImm`; for `JMP [mem]` (a load, then a jump): `afterStep_jumpLoad_rip`,
`AgreesExcept.afterStep_jumpLoad` (`[.rip]`), `ReadyToStep.afterStep_jumpLoad`; for `PUSH [mem]` (a
load, then a push): `afterStep_pushLoad_rip`, `Operand.read_afterStep_pushLoad_rsp`,
`Operand.read_afterStep_pushLoad_mem`, `AgreesExcept.afterStep_pushLoad`,
`ReadyToStep.afterStep_pushLoad` and `StepEffect.of_pushLoad`; for `PUSH word [mem]` (2 bytes,
`pushState16`) the same with `pushLoad16`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-! ### After a CALL step -/

/-- A taken near branch (RIP := `target`, `Branch_Taken`) changes only RIP (besides the
bookkeeping). -/
theorem AgreesExcept.of_jump (t : RamState) (target : BitVec 64) :
    AgreesExcept [.rip] t { t with RIP := target, Branch_Taken := true } := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r => rfl
    | flags => rfl
    | rip => exact absurd (by simp) hc
    | mem addr len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => rfl
  · simp only [fixedPart, beforeFetch, resetStepFields]

/-- The state a CALL form pushes from, `t` being the state it starts from: `Next_IP` set, after
the read of the pointer (`dataAccess t "load"`) for `call [mem]` (`load = true`). -/
def callFrom (load : Bool) (t : RamState) (nextIP : BitVec 64) : RamState :=
  withNextIP (cond load (dataAccess t "load") t) nextIP

/-- The state a CALL form pushes from agrees with the start state everywhere. -/
theorem AgreesExcept.of_callFrom (load : Bool) (s : RamState) (k : Nat) (nextIP : BitVec 64) :
    AgreesExcept [] s (callFrom load (afterFetches (beforeFetch s) k) nextIP) := by
  cases load
  · exact AgreesExcept.prepare s k nextIP
  · refine ⟨fun c _ _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
    · cases c <;> first | rfl | exact fun _ _ => rfl
    · simp only [fixedPart, X86Proofs.callFrom, cond, withNextIP, dataAccess, afterFetches,
        beforeFetch, resetStepFields]

/-- After a CALL step, RIP is the target. -/
theorem afterStep_call_rip (s : RamState) (load : Bool) (length : Nat)
    (nextIP target : BitVec 64) :
    (afterStep s length fun t => callState (callFrom load t nextIP) nextIP target).RIP =
      target := by
  simp [afterStep, finishStep, callState, pushState, Operand.write, stackAccess]

/-- Memory after a CALL step: the return address written at RSP - 8. -/
@[simp] theorem afterStep_call_external (s : RamState) (load : Bool) (length : Nat)
    (nextIP target : BitVec 64) :
    (afterStep s length fun t => callState (callFrom load t nextIP) nextIP target).external =
      memStore s.external (pushAddr s) nextIP := by
  cases load <;> rfl

/-- After a CALL step, RSP is the old RSP - 8. -/
theorem Operand.read_afterStep_call_rsp (s : RamState) (load : Bool) (length : Nat)
    (nextIP target : BitVec 64) :
    (Operand.reg 4 : Operand 64).read
      (afterStep s length fun t => callState (callFrom load t nextIP) nextIP target) =
      pushAddr s := by
  rw [Operand.read_afterStep]
  cases load <;> exact Operand.read_write_reg64_self _ _ _

/-- After a CALL step, the 8 bytes at the old RSP - 8 hold the return address. -/
theorem Operand.read_afterStep_call_mem (s : RamState) (load : Bool) (length : Nat)
    (nextIP target : BitVec 64) :
    (Operand.mem (pushAddr s) : Operand 64).read
      (afterStep s length fun t => callState (callFrom load t nextIP) nextIP target) =
      nextIP := by
  simp only [Operand.read, afterStep_call_external]
  exact memLoad_memStore _ _ (by decide) (by decide) nextIP

/-- A CALL step changes only RSP, the 8 bytes at RSP - 8 and RIP (besides the bookkeeping). -/
theorem AgreesExcept.afterStep_call (s : RamState) (load : Bool) (length : Nat)
    (nextIP target : BitVec 64) :
    AgreesExcept [.reg 4, .mem (pushAddr s) 8, .rip] s
      (afterStep s length fun t => callState (callFrom load t nextIP) nextIP target) := by
  have hsub : ∀ c ∈ ([] ++ [.reg 4, .mem (pushAddr s) 8] ++ [.rip] ++ [.rip] : List Component),
      c ∈ [.reg 4, .mem (pushAddr s) 8, .rip] := by simp
  cases load <;>
  exact ((((AgreesExcept.of_callFrom _ s (length + 1) nextIP).trans
    (AgreesExcept.of_pushState _ nextIP)).trans
    (AgreesExcept.of_jump _ target)).trans (AgreesExcept.of_finishStep _)).mono hsub

/-- Preservation for a CALL: if the 8 bytes at RSP - 8 lie below 4 GiB and outside the page
tables, the state after the step is ready to step again. -/
theorem ReadyToStep.afterStep_call [Bindings] {s : RamState} (h : ReadyToStep s) (load : Bool)
    (length : Nat) (nextIP target : BitVec 64)
    (hlow : (pushAddr s).toNat + 8 ≤ 2^32)
    (htables : PageTableEntriesApart (pushAddr s).toNat 8) :
    ReadyToStep (afterStep s length fun t => callState (callFrom load t nextIP) nextIP target) :=
  h.of_agreesExcept (AgreesExcept.afterStep_call s load length nextIP target) (by
    rw [afterStep_call_external]
    exact IdentityPageTableMemory.memStore h.memory.tables _ _ hlow htables)

/-! ### After a RET step -/

/-- After a RET step, RIP is the 8 bytes that were at RSP. -/
theorem afterStep_ret_rip {s : RamState} (length : Nat)
    (nextIP : BitVec 64) :
    (afterStep s length fun t => retState (withNextIP t nextIP)).RIP = stackTop s := by
  simp [afterStep, finishStep, retState, Operand.write, dataAccess, withNextIP, afterFetches,
    beforeFetch, resetStepFields]
  rfl

/-- A RET step leaves memory unchanged. -/
@[simp] theorem afterStep_ret_external (s : RamState) (length : Nat) (nextIP : BitVec 64) :
    (afterStep s length fun t => retState (withNextIP t nextIP)).external = s.external := rfl

/-- After a RET step, RSP is the old RSP + 8. -/
theorem Operand.read_afterStep_ret_rsp (s : RamState) (length : Nat) (nextIP : BitVec 64) :
    (Operand.reg 4 : Operand 64).read
      (afterStep s length fun t => retState (withNextIP t nextIP)) = stackPtr s + 8 := by
  rw [Operand.read_afterStep]
  exact Operand.read_write_reg64_self _ _ _

/-- A RET step changes only RSP and RIP (besides the bookkeeping). -/
theorem AgreesExcept.afterStep_ret (s : RamState) (length : Nat) (nextIP : BitVec 64) :
    AgreesExcept [.reg 4, .rip] s
      (afterStep s length fun t => retState (withNextIP t nextIP)) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r =>
      have h4 : (4 : BitVec 5) ≠ r := fun h => hc (h ▸ List.mem_cons_self)
      have := Operand.read_write_reg_of_ne (m := 64)
        { dataAccess { afterFetches (beforeFetch s) (length + 1) with Next_IP := nextIP } "load" with
          RIP := stackTop { afterFetches (beforeFetch s) (length + 1) with Next_IP := nextIP },
          Branch_Taken := true } h4 (stackPtr s + 8)
      simp only [Operand.read_reg64] at this
      exact this
    | flags => rfl
    | rip => exact absurd (by simp) hc
    | mem addr len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => rfl
  · simp only [fixedPart, afterStep, finishStep, retState, Operand.write, dataAccess, withNextIP,
      afterFetches, beforeFetch, resetStepFields]

/-- Preservation for a RET. -/
theorem ReadyToStep.afterStep_ret [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t => retState (withNextIP t nextIP)) :=
  h.of_agreesExcept (AgreesExcept.afterStep_ret s length nextIP) h.memory.tables

/-! ### After a RET imm16 step -/

/-- After a `RET imm16` step, RIP is the 8 bytes that were at RSP. -/
theorem afterStep_retImm_rip {s : RamState} (length : Nat) (nextIP : BitVec 64)
    (imm : BitVec 16) :
    (afterStep s length fun t => retImmState (withNextIP t nextIP) imm).RIP = stackTop s := by
  simp [afterStep, finishStep, retImmState, Operand.write, dataAccess, withNextIP, afterFetches,
    beforeFetch, resetStepFields]
  rfl

/-- A `RET imm16` step leaves memory unchanged. -/
@[simp] theorem afterStep_retImm_external (s : RamState) (length : Nat) (nextIP : BitVec 64)
    (imm : BitVec 16) :
    (afterStep s length fun t => retImmState (withNextIP t nextIP) imm).external = s.external :=
  rfl

/-- After a `RET imm16` step, RSP is the old RSP + 8 + `imm`. -/
theorem Operand.read_afterStep_retImm_rsp (s : RamState) (length : Nat) (nextIP : BitVec 64)
    (imm : BitVec 16) :
    (Operand.reg 4 : Operand 64).read
      (afterStep s length fun t => retImmState (withNextIP t nextIP) imm) =
      stackPtr s + 8 + imm.setWidth 64 := by
  rw [Operand.read_afterStep]
  exact Operand.read_write_reg64_self _ _ _

/-- A `RET imm16` step changes only RSP and RIP (besides the bookkeeping). -/
theorem AgreesExcept.afterStep_retImm (s : RamState) (length : Nat) (nextIP : BitVec 64)
    (imm : BitVec 16) :
    AgreesExcept [.reg 4, .rip] s
      (afterStep s length fun t => retImmState (withNextIP t nextIP) imm) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r =>
      have h4 : (4 : BitVec 5) ≠ r := fun h => hc (h ▸ List.mem_cons_self)
      have := Operand.read_write_reg_of_ne (m := 64)
        { dataAccess { afterFetches (beforeFetch s) (length + 1) with Next_IP := nextIP } "load" with
          RIP := stackTop { afterFetches (beforeFetch s) (length + 1) with Next_IP := nextIP },
          Branch_Taken := true } h4 (stackPtr s + 8 + imm.setWidth 64)
      simp only [Operand.read_reg64] at this
      exact this
    | flags => rfl
    | rip => exact absurd (by simp) hc
    | mem addr len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => rfl
  · simp only [fixedPart, afterStep, finishStep, retImmState, Operand.write, dataAccess,
      withNextIP, afterFetches, beforeFetch, resetStepFields]

/-- Preservation for a `RET imm16`. -/
theorem ReadyToStep.afterStep_retImm [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (nextIP : BitVec 64) (imm : BitVec 16) :
    ReadyToStep (afterStep s length fun t => retImmState (withNextIP t nextIP) imm) :=
  h.of_agreesExcept (AgreesExcept.afterStep_retImm s length nextIP imm) h.memory.tables

/-! ### After an indirect JMP through memory -/

/-- After a step whose form reads memory (`dataAccess t "load"`) and then jumps to `target`
(`JMP [mem]`, `Instructions/Jmp/Generated/M`), RIP is `target`. -/
theorem afterStep_jumpLoad_rip (s : RamState) (length : Nat) (nextIP target : BitVec 64) :
    (afterStep s length fun t => jumpState (dataAccess t "load") nextIP target).RIP = target := by
  simp [afterStep, finishStep, jumpState, dataAccess]

/-- A step whose form reads memory and then jumps changes only RIP (besides the
bookkeeping). -/
theorem AgreesExcept.afterStep_jumpLoad (s : RamState) (length : Nat)
    (nextIP target : BitVec 64) :
    AgreesExcept [.rip] s
      (afterStep s length fun t => jumpState (dataAccess t "load") nextIP target) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r => rfl
    | flags => rfl
    | rip => exact absurd (by simp) hc
    | mem addr len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => rfl
  · simp only [fixedPart, afterStep, finishStep, jumpState, dataAccess, afterFetches,
      beforeFetch, resetStepFields]

/-- Preservation for a step whose form reads memory and then jumps. -/
theorem ReadyToStep.afterStep_jumpLoad [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (nextIP target : BitVec 64) :
    ReadyToStep (afterStep s length fun t => jumpState (dataAccess t "load") nextIP target) :=
  h.of_agreesExcept (AgreesExcept.afterStep_jumpLoad s length nextIP target) h.memory.tables

/-! ### After a push of a value read from memory -/

/-- After a step whose form reads memory and then pushes `v` (`PUSH [mem]`,
`Instructions/Push/Generated/M`; the push starts from `callFrom true t nextIP`), RIP is
`nextIP`. -/
theorem afterStep_pushLoad_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (v nextIP : BitVec 64) :
    (afterStep s length fun t => pushState (callFrom true t nextIP) v).RIP = nextIP := by
  simp [afterStep, finishStep, pushState, callFrom, Operand.write, stackAccess, dataAccess,
    withNextIP, afterFetches, beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- Memory after such a step: the 8 bytes at RSP - 8 written. -/
@[simp] theorem afterStep_pushLoad_external (s : RamState) (length : Nat) (v nextIP : BitVec 64) :
    (afterStep s length fun t => pushState (callFrom true t nextIP) v).external =
      memStore s.external (pushAddr s) v := rfl

/-- After such a step, RSP is the old RSP - 8. -/
theorem Operand.read_afterStep_pushLoad_rsp (s : RamState) (length : Nat) (v nextIP : BitVec 64) :
    (Operand.reg 4 : Operand 64).read
      (afterStep s length fun t => pushState (callFrom true t nextIP) v) = pushAddr s := by
  rw [Operand.read_afterStep, pushState, Operand.read_write_reg64_self]
  rfl

/-- After such a step, the 8 bytes at the old RSP - 8 hold the value pushed. -/
theorem Operand.read_afterStep_pushLoad_mem (s : RamState) (length : Nat) (v nextIP : BitVec 64) :
    (Operand.mem (pushAddr s) : Operand 64).read
      (afterStep s length fun t => pushState (callFrom true t nextIP) v) = v := by
  simp only [Operand.read, afterStep_pushLoad_external]
  exact memLoad_memStore _ _ (by decide) (by decide) v

/-- Such a step changes only RSP, the 8 bytes at RSP - 8 and RIP (besides the bookkeeping). -/
theorem AgreesExcept.afterStep_pushLoad (s : RamState) (length : Nat) (v nextIP : BitVec 64) :
    AgreesExcept [.reg 4, .mem (pushAddr s) 8, .rip] s
      (afterStep s length fun t => pushState (callFrom true t nextIP) v) :=
  ((AgreesExcept.of_callFrom true s (length + 1) nextIP).trans
    (AgreesExcept.of_pushState _ v)).trans (AgreesExcept.of_finishStep _)

/-- Preservation for such a step, if the 8 bytes at RSP - 8 lie below 4 GiB and outside the page
tables. -/
theorem ReadyToStep.afterStep_pushLoad [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (v nextIP : BitVec 64)
    (hlow : (pushAddr s).toNat + 8 ≤ 2^32)
    (htables : PageTableEntriesApart (pushAddr s).toNat 8) :
    ReadyToStep (afterStep s length fun t => pushState (callFrom true t nextIP) v) :=
  h.of_agreesExcept (AgreesExcept.afterStep_pushLoad s length v nextIP) (by
    rw [afterStep_pushLoad_external]
    exact IdentityPageTableMemory.memStore h.memory.tables _ _ hlow htables)

/--
The step of a form that reads memory and pushes `v s` at `p` with its effect, from its step
theorem (as `StepEffect.of_push`, for any precondition `pre` that gives `PushPre`): the effect
`pushEffect (fun _ => p + len) v`.
-/
theorem StepEffect.of_pushLoad [Bindings] {pre : RamState → Prop} {p : BitVec 64}
    {bytes : List UInt8} {len : Nat} (v : RamState → BitVec 64)
    (hpush : ∀ s, pre s → PushPre p len s)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → pre s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        pushState (callFrom true t (BitVec.add p (BitVec.ofNat 64 len))) (v s)))) :
    StepEffect pre (codeRange p bytes) (pushEffect (fun _ => p + BitVec.ofNat 64 len) v) := by
  intro s h hcode hpre
  have hp := hpush s hpre
  exact ⟨_, hstep s h hcode hpre,
    ReadyToStep.afterStep_pushLoad h _ _ _ hp.write.low hp.write.tables,
    ⟨afterStep_pushLoad_rip h _ _ _, ⟨Operand.read_afterStep_pushLoad_rsp _ _ _ _,
      Operand.read_afterStep_pushLoad_mem _ _ _ _⟩, trivial,
      (pushEffect_components _ v s).symm ▸ AgreesExcept.afterStep_pushLoad _ _ _ _⟩⟩

/-- After a step whose form reads memory and then pushes the 16-bit `v` (`PUSH word [mem]`,
`Instructions/Push/Generated/M16`; the push starts from `callFrom true t nextIP`), RIP is
`nextIP`. -/
theorem afterStep_pushLoad16_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (v : BitVec 16) (nextIP : BitVec 64) :
    (afterStep s length fun t => pushState16 (callFrom true t nextIP) v).RIP = nextIP := by
  simp [afterStep, finishStep, pushState16, callFrom, Operand.write, stackAccess, dataAccess,
    withNextIP, afterFetches, beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- Memory after such a step: the 2 bytes at RSP - 2 written. -/
@[simp] theorem afterStep_pushLoad16_external (s : RamState) (length : Nat) (v : BitVec 16)
    (nextIP : BitVec 64) :
    (afterStep s length fun t => pushState16 (callFrom true t nextIP) v).external =
      memStore s.external (pushAddr16 s) v := rfl

/-- After such a step, RSP is the old RSP - 2. -/
theorem Operand.read_afterStep_pushLoad16_rsp (s : RamState) (length : Nat) (v : BitVec 16)
    (nextIP : BitVec 64) :
    (Operand.reg 4 : Operand 64).read
      (afterStep s length fun t => pushState16 (callFrom true t nextIP) v) = pushAddr16 s := by
  rw [Operand.read_afterStep, pushState16, Operand.read_write_reg64_self]
  rfl

/-- After such a step, the 2 bytes at the old RSP - 2 hold the value pushed. -/
theorem Operand.read_afterStep_pushLoad16_mem (s : RamState) (length : Nat) (v : BitVec 16)
    (nextIP : BitVec 64) :
    (Operand.mem (pushAddr16 s) : Operand 16).read
      (afterStep s length fun t => pushState16 (callFrom true t nextIP) v) = v := by
  simp only [Operand.read, afterStep_pushLoad16_external]
  exact memLoad_memStore _ _ (by decide) (by decide) v

/-- Such a step changes only RSP, the 2 bytes at RSP - 2 and RIP (besides the bookkeeping). -/
theorem AgreesExcept.afterStep_pushLoad16 (s : RamState) (length : Nat) (v : BitVec 16)
    (nextIP : BitVec 64) :
    AgreesExcept [.reg 4, .mem (pushAddr16 s) 2, .rip] s
      (afterStep s length fun t => pushState16 (callFrom true t nextIP) v) :=
  ((AgreesExcept.of_callFrom true s (length + 1) nextIP).trans
    (AgreesExcept.of_pushState16 _ v)).trans (AgreesExcept.of_finishStep _)

/-- Preservation for such a step, if the 2 bytes at RSP - 2 lie below 4 GiB and outside the page
tables. -/
theorem ReadyToStep.afterStep_pushLoad16 [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (v : BitVec 16) (nextIP : BitVec 64)
    (hlow : (pushAddr16 s).toNat + 2 ≤ 2^32)
    (htables : PageTableEntriesApart (pushAddr16 s).toNat 2) :
    ReadyToStep (afterStep s length fun t => pushState16 (callFrom true t nextIP) v) :=
  h.of_agreesExcept (AgreesExcept.afterStep_pushLoad16 s length v nextIP) (by
    rw [afterStep_pushLoad16_external]
    exact IdentityPageTableMemory.memStore h.memory.tables _ _ hlow htables)

/--
The step of a form that reads memory and pushes the 16-bit `v s` at `p` with its effect, from its
step theorem (as `StepEffect.of_pushLoad`, for any precondition `pre` that gives `Push16Pre`): the
effect `push16Effect (fun _ => p + len) v`.
-/
theorem StepEffect.of_pushLoad16 [Bindings] {pre : RamState → Prop} {p : BitVec 64}
    {bytes : List UInt8} {len : Nat} (v : RamState → BitVec 16)
    (hpush : ∀ s, pre s → Push16Pre p len s)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → pre s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        pushState16 (callFrom true t (BitVec.add p (BitVec.ofNat 64 len))) (v s)))) :
    StepEffect pre (codeRange p bytes) (push16Effect (fun _ => p + BitVec.ofNat 64 len) v) := by
  intro s h hcode hpre
  have hp := hpush s hpre
  exact ⟨_, hstep s h hcode hpre,
    ReadyToStep.afterStep_pushLoad16 h _ _ _ hp.write.low hp.write.tables,
    ⟨afterStep_pushLoad16_rip h _ _ _, ⟨Operand.read_afterStep_pushLoad16_rsp _ _ _ _,
      Operand.read_afterStep_pushLoad16_mem _ _ _ _⟩, trivial,
      (push16Effect_components _ v s).symm ▸ AgreesExcept.afterStep_pushLoad16 _ _ _ _⟩⟩

/-! ### Step theorems -/

/-- The state a CALL or RET form starts from: ready for data accesses, with the flat stack
segment. -/
theorem call_start [Bindings] {s : RamState} (h : ReadyToStep s) (k : Nat) :
    DataReady (afterFetches (beforeFetch s) k) ∧ (afterFetches (beforeFetch s) k).SS = userStackSegment :=
  ⟨h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables, h.cpu.ss⟩

/--
Layer 3 for `call rel32` (`E8`, displacement `disp`): one `step` pushes RIP + 5 and jumps to
RIP + 5 + sext disp. Needs the target below 4 GiB and the 8 bytes at RSP - 8 writable in place.
-/
theorem call_rel32_step [Bindings] (s : RamState) (h : ReadyToStep s) (disp : BitVec 32)
    (hcode : BytesAt s s.RIP (0xE8 :: immBytes 32 disp)) (hlow : s.RIP.toNat + 5 ≤ 2^32)
    (htarget : (BitVec.add (BitVec.add s.RIP 5#64) (disp.signExtend 64)).toNat < 2^32)
    (hw : MemWritable s (pushAddr s) 8) :
    X86.Machine.step s = some (.next (afterStep s 5 fun t =>
      callState (callFrom false t (BitVec.add s.RIP 5#64)) (BitVec.add s.RIP 5#64)
        (BitVec.add (BitVec.add s.RIP 5#64) (disp.signExtend 64)))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0xE8 :: immBytes 32 disp) := hcode
  have hlow' : s.RIP.toNat + (0xE8 :: immBytes 32 disp).length ≤ 2^32 := by
    simpa using hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures (k : Nat) : DecoderFeatures (afterFetches (beforeFetch s) k) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0xE8, afterFetches (beforeFetch s) 2) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) 1 hf hc hlow' 0 (by simp) (by simp)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at this
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 32).run (afterFetches (beforeFetch s) 2) =
      (.ok disp, afterFetches (beforeFetch s) 6) :=
    memFetch_run_of_bytesAt_imm (beforeFetch s) 2 hf hc hlow' 32 (by decide) disp 1
      (immBytes_getElem?_append [0xE8] disp) (by simp) (by decide)
  obtain ⟨hd, hss⟩ := call_start h 6
  have hdecode := decodeLegacy0_run_of_opcodeE8 _ _ _ (legacyContext s.DS) rfl f1 (hmode 2)
  rw [decodeLegacy0OpcodeE8_run_of_call _ _ _ (hmode 2) (hfeatures 2)] at hdecode
  rw [call_rel32_form _ _ _ _ disp rfl rfl f2 (hmode 6) hd hss
    (by rw [add_ofNat_add]; exact htarget) (hw.of_external_eq rfl), add_ofNat_add] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h _ (immBytes 32 disp)
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode ((hmode 6).of_cs_lma_eq rfl rfl)

/--
Layer 3 for `call r64` (`pre FF /2`, `mod = 3`), for any prefix list `pre` the prefix scan covers
(e.g. `41`, REX.B) and any register: one `step` pushes RIP + L (L = `pre.length + 2`) and
jumps to the value of register `rm` (extended by REX.B). Needs that value below 4 GiB and the
8 bytes at RSP - 8 writable in place.
-/
theorem call_r64_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hmode64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2)
    (hcode : BytesAt s s.RIP (pre ++ [0xFF, modrm]))
    (hlow : s.RIP.toNat + (pre.length + 2) ≤ 2^32)
    (htarget : ((Operand.reg (gprNumber (scanContext s.DS (PrefixSegments.ofState s) pre).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) pre).rex_b3 (modrmRm modrm)) : Operand 64).read s).toNat < 2^32)
    (hw : MemWritable s (pushAddr s) 8) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let src : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2) fun t =>
      callState (callFrom false t (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2))))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2))) (src.read s))) := by
  intro ctx src
  have hlen' : (pre ++ [0xFF, modrm]).length = pre.length + 2 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xFF, modrm]).length ≤ 2^32 := by rw [hlen']; exact hlow
  have hdecode := decodeLegacy0_run_of_FF_call_register s h _ pre.length modrm hmod hreg hcode hlow'
    (by simp) (by simp) (by omega) ctx hrex2
  have hmode : In64BitMode (afterFetches (beforeFetch s) (pre.length + 3)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  obtain ⟨hd, hss⟩ := call_start h (pre.length + 3)
  rw [call_r_form _ _ _ _ hmode64 hlock hmode hd hss htarget (hw.of_external_eq rfl)]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xFF [modrm] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    (hmode.of_cs_lma_eq rfl rfl)

/--
Layer 3 for `call [mem]` (`pre FF /2`, `mod ≠ 3`) with any segment prefix (`SegAddrContext`: an
FS or GS prefix, whose segment must be ready, or none): as `call_m64_step`, the pointer read at the
operand's linear address `segAddr ctx (am.addrAt s L)` (the return address is pushed on SS, which
takes no override).
-/
theorem call_m64_seg_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0xFF :: am.modrm 2 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt s (pre.length + 2 + am.tail.length))) 8)
    (htarget : ((Operand.mem (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt s (pre.length + 2 + am.tail.length))) : Operand 64).read s).toNat < 2^32)
    (hw : MemWritable s (pushAddr s) 8) :
    let L := pre.length + 2 + am.tail.length
    X86.Machine.step s = some (.next (afterStep s L fun t =>
      callState (callFrom true t (BitVec.add s.RIP (BitVec.ofNat 64 L)))
        (BitVec.add s.RIP (BitVec.ofNat 64 L))
        ((Operand.mem (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt s L)) :
          Operand 64).read s))) := by
  intro L
  have hlen' : (pre ++ 0xFF :: am.modrm 2 :: am.tail).length = L := by simp [L]; omega
  have hlow' : s.RIP.toNat + (pre ++ 0xFF :: am.modrm 2 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_FF_call_memory s h _ pre.length (am.modrm 2)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode hlow'
    (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea_seg s h pre 0xFF 2 am hv [] _ hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = L + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (L + 1)
  obtain ⟨hd, hss⟩ := call_start h (L + 1)
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s) (BitVec.add s.RIP (BitVec.ofNat 64 L))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [call_m_seg_form _ t _ _ _ _ hctx.mode64 haddr hlock _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) hd hss (hread.of_external_eq rfl) htarget
    (hw.of_external_eq rfl)] at hdecode
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xFF _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

/--
Layer 3 for `call [mem]` at address size 32 (a `67` prefix in `pre`), with any segment prefix: as
`call_m64_seg_step`, the pointer read at `segAddr ctx (am.addrAt32 s L)` (`AddrMode.addr32`; the
return address is still pushed at RSP - 8, the stack's address size being 64).
-/
theorem call_m64_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0xFF :: am.modrm 2 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt32 s (pre.length + 2 + am.tail.length))) 8)
    (htarget : ((Operand.mem (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt32 s (pre.length + 2 + am.tail.length))) : Operand 64).read s).toNat < 2^32)
    (hw : MemWritable s (pushAddr s) 8) :
    let L := pre.length + 2 + am.tail.length
    X86.Machine.step s = some (.next (afterStep s L fun t =>
      callState (callFrom true t (BitVec.add s.RIP (BitVec.ofNat 64 L)))
        (BitVec.add s.RIP (BitVec.ofNat 64 L))
        ((Operand.mem (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre) (am.addrAt32 s L)) :
          Operand 64).read s))) := by
  intro L
  have hlen' : (pre ++ 0xFF :: am.modrm 2 :: am.tail).length = L := by simp [L]; omega
  have hlow' : s.RIP.toNat + (pre ++ 0xFF :: am.modrm 2 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hdecode := decodeLegacy0_run_of_FF_call_memory s h _ pre.length (am.modrm 2)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode hlow'
    (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea32_seg s h pre 0xFF 2 am hv [] _ hctx (by simpa using hcode)
    (by simpa using hlow') (by omega)
  rw [show pre.length + 3 + am.tail.length = L + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (L + 1)
  obtain ⟨hd, hss⟩ := call_start h (L + 1)
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s) (BitVec.add s.RIP (BitVec.ofNat 64 L))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  rw [call_m_seg_form _ t _ _ _ _ hctx.mode64 haddr hlock _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) hd hss (hread.of_external_eq rfl) htarget
    (hw.of_external_eq rfl)] at hdecode
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xFF _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

/--
Layer 3 for `call [mem]` (`pre FF /2`, `mod ≠ 3`), for any prefix list `pre` the prefix scan
covers and any addressing shape `am` (e.g. no prefix, `[rip + disp32]`): one `step` reads the
8-byte pointer at `am.addrAt s L` (L = `pre.length + 2 + am.tail.length`), pushes RIP + L and
jumps to the pointer. Needs the pointer readable, its value below 4 GiB, and the 8 bytes at
RSP - 8 writable in place (`call_m64_seg_step` without a segment prefix).
-/
theorem call_m64_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid) (hctx : AddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0xFF :: am.modrm 2 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 2 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (pre.length + 2 + am.tail.length)) 8)
    (htarget : ((Operand.mem (am.addrAt s (pre.length + 2 + am.tail.length)) :
      Operand 64).read s).toNat < 2^32)
    (hw : MemWritable s (pushAddr s) 8) :
    let L := pre.length + 2 + am.tail.length
    X86.Machine.step s = some (.next (afterStep s L fun t =>
      callState (callFrom true t (BitVec.add s.RIP (BitVec.ofNat 64 L)))
        (BitVec.add s.RIP (BitVec.ofNat 64 L))
        ((Operand.mem (am.addrAt s L) : Operand 64).read s))) := by
  have hstep := call_m64_seg_step s h pre hpre hlen haddr hrex2 hlock am hv hctx.toSeg hcode hlow
    (by rw [segAddr_of_not hctx.seg]; exact hread) (by rw [segAddr_of_not hctx.seg]; exact htarget)
    hw
  simp only [segAddr_of_not hctx.seg] at hstep
  exact hstep

/-- Layer 3 for `ret` (`C3`): one `step` pops the 8 bytes at RSP into RIP and sets RSP to
RSP + 8. Needs them readable and their value below 4 GiB. -/
theorem ret_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hcode : BytesAt s s.RIP [0xC3]) (hlow : s.RIP.toNat + 1 ≤ 2^32)
    (hr : MemReadable s (stackPtr s) 8) (htarget : (stackTop s).toNat < 2^32) :
    X86.Machine.step s = some (.next (afterStep s 1 fun t =>
      retState (withNextIP t (BitVec.add s.RIP 1#64)))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0xC3] := hcode
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 2) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  have f1 : (Mem_Fetch s.RIP 8).run (afterFetches (beforeFetch s) 1) =
      (.ok 0xC3, afterFetches (beforeFetch s) 2) := by
    have := memFetch_run_of_bytesAt (beforeFetch s) 1 hf hc hlow 0 (by simp) (by decide)
    rwa [show BitVec.add (beforeFetch s).RIP (BitVec.ofNat 64 0) = (beforeFetch s).RIP
      from BitVec.add_zero _] at this
  obtain ⟨hd, hss⟩ := call_start h 2
  have hdecode := decodeLegacy0_run_of_opcodeC3 _ _ _ (legacyContext s.DS) rfl f1 (hmode 2)
  rw [decodeLegacy0OpcodeC3_run_of_ret _ _ _ (hmode 2) hfeatures,
    ret_form _ _ _ rfl rfl (hmode 2) hd hss (hr.of_external_eq rfl) htarget] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xC3 [] (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode
    hlow hdecode ((hmode 2).of_cs_lma_eq rfl rfl)

end X86Proofs
