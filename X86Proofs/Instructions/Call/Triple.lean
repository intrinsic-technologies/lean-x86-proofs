import X86Proofs.Instructions.Call.Step
import X86Proofs.Instructions.Call.Encode
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Push.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Program.ReadWrite.Rmw
import X86Proofs.Program.Compose

/-!
# CALL and RET triples

| Instruction | Bytes | Length | Triple | Precondition | Effect |
|---|---|---|---|---|---|
| `call rel32` | `encodeCallRel32 disp` (`E8 cd`) | 5 | `call_rel32_triple` | `PushPre p 5` (+ `htarget`) | `callEffect (fun _ => branchTarget p 5 (sext disp)) (p + 5)` |
| `call r64` | `FF /2` (`mod = 3`) | 2 | `call_r64_triple_of_bytes` | `CallPre p 2 target` | `callEffect target (p + 2)` |
| `call r64` | `REX FF /2` | 3 | `call_r64_rex_triple_of_bytes` | `CallPre p 3 target` | `callEffect target (p + 3)` |
| `call r64` | `encodeCallR64 r` | 2 or 3 | `call_r64_triple` | `CallPre p len target` | as above |
| `call [am]` | `encodeCallM64 am` (`FF /2`) | `2 + tail` | `call_m64_triple` | `CallMemPre p am` | `callEffect (callMemPtr p am) (p + len)` |
| `call [rip+d]` | `encodeCallM64 (.rip d)` (`FF 15 d32`) | 6 | `call_m64_rip_triple` | `CallMemPre p (.rip d)` | `callEffect (callMemPtr p (.rip d)) (p + 6)` |
| `call fs:[am]` | `r.prefixByte :: encodeCallM64 am` (`64`/`65 FF /2`) | `3 + tail` | `call_m64_seg_triple` | `CallMemSegPre p r base am` | `callEffect (callMemSegPtr p base am) (p + len)` |
| `call [am]`, address size 32 | `0x67 :: encodeCallM64 am` (`67 FF /2`) | `3 + tail` | `call_m64_a32_triple` | `CallMemA32Pre p am` | `callEffect (callMemA32Ptr p am) (p + len)` |
| `ret` | `C3` | 1 | `ret_triple` | `RetPre p` | `retEffect` |

How the stack is stated, so that a CALL's push and a RET's pop can be matched:
- `callEffect target ret = pushEffect target (fun _ => ret)`: writes RSP := `pushAddr s`
  (RSP - 8) and the 8 bytes at `pushAddr s` := `ret` (the return address `p + len`), RIP :=
  `target s`.
- `retEffect s`: RIP := `stackTop s` (the 8 bytes at RSP, read in the start state), writes RSP :=
  `stackPtr s + 8`.
- `callEffect_stack`: after a call's effect, `stackTop s' = ret` and `stackPtr s' + 8 = stackPtr s`.

Preconditions: `CallPre p len target` = `PushPre p len` (the 8 bytes at RSP - 8 writable in place
and apart from the code) and `target` below 4 GiB (the canonical check); `CallMemPre` adds the
pointer's 8 bytes readable (`CallMemSegPre`: at `base + am.addr …` through an FS or GS override,
whose segment `r` is ready with base `base`; `CallMemA32Pre`: at `am.addr32 …` behind `67`);
`RetPre p` = `PopPre p` and `stackTop` below 4 GiB. CET (shadow stack, end-branch tracking) is
off under `ReadyToStep`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-! ### Effects -/

/-- The effect of a near call to `target s` that pushes the return address `ret`: RSP := RSP - 8,
the 8 bytes at the old RSP - 8 := `ret`, RIP := `target s`. -/
abbrev callEffect (target : RamState → BitVec 64) (ret : BitVec 64) : RamState → Effect :=
  pushEffect target fun _ => ret

/-- The precondition of a call of `len` bytes at `p` to `target s`: the push of the return
address (`PushPre`), and the target below 4 GiB (lean-x86's canonical check). -/
abbrev CallPre (p : BitVec 64) (len : Nat) (target : RamState → BitVec 64) (s : RamState) :
    Prop :=
  PushPre p len s ∧ (target s).toNat < 2^32

/-- The effect of `ret`: RIP := the 8 bytes at RSP (`stackTop`), RSP := RSP + 8. -/
def retEffect (s : RamState) : Effect where
  rip := stackTop s
  writes := [⟨(Operand.reg 4 : Operand 64), stackPtr s + 8⟩]

@[simp] theorem retEffect_components (s : RamState) :
    (retEffect s).components = [.reg 4, .rip] := rfl

/-- The precondition of `ret` at `p`: RIP = `p`, the 8 bytes at RSP readable (`PopPre`), and the
address they hold below 4 GiB. -/
abbrev RetPre (p : BitVec 64) (s : RamState) : Prop :=
  PopPre p s ∧ (stackTop s).toNat < 2^32

/-- After a call's effect, the stack top is the return address and popping it restores RSP: what
a `ret` at the end of the callee sees, if the callee leaves RSP and the slot as the call left
them. -/
theorem callEffect_stack {target : RamState → BitVec 64} {ret : BitVec 64} {s s' : RamState}
    (h : (callEffect target ret s).Holds s s') :
    stackTop s' = ret ∧ stackPtr s' + 8 = stackPtr s := by
  obtain ⟨-, ⟨hrsp, hmem⟩, -, -⟩ := h
  simp only [Operand.read_reg64] at hrsp
  have hsp : stackPtr s' = pushAddr s := hrsp
  refine ⟨?_, ?_⟩
  · rw [stackTop, hsp]
    exact hmem
  · rw [hsp, pushAddr, BitVec.sub_add_cancel]

/-! ### From step theorems to effect steps and triples -/

/--
The step of a CALL form at `p` with its effect, from its step theorem. If from every ready state
with the instruction `bytes` at `p` and `pre` (which gives `PushPre`), one `step` runs the form,
ending in a call to `target s` that pushes `p + len`, then that step reaches a ready state with the
effect `callEffect target (p + len)`.
-/
theorem StepEffect.of_call [Bindings] {pre : RamState → Prop} {p : BitVec 64}
    {bytes : List UInt8} {len : Nat} (load : Bool) (target : RamState → BitVec 64)
    (hpush : ∀ s, pre s → PushPre p len s)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → pre s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        callState (callFrom load t (BitVec.add p (BitVec.ofNat 64 len)))
          (BitVec.add p (BitVec.ofNat 64 len)) (target s)))) :
    StepEffect pre (codeRange p bytes) (callEffect target (p + BitVec.ofNat 64 len)) := by
  intro s h hcode hpre
  have hp := hpush s hpre
  exact ⟨_, hstep s h hcode hpre,
    ReadyToStep.afterStep_call h load _ _ _ hp.write.low hp.write.tables,
    ⟨afterStep_call_rip _ _ _ _ _, ⟨Operand.read_afterStep_call_rsp _ _ _ _ _,
      Operand.read_afterStep_call_mem _ _ _ _ _⟩, trivial,
      (pushEffect_components _ _ s).symm ▸ AgreesExcept.afterStep_call _ _ _ _ _⟩⟩

/--
The triple of a CALL form at `p`, from its step theorem (as `StepEffect.of_call`): the effect
`callEffect target (p + len)`, which avoids the instruction's `len` bytes (`pushEffect_avoids`).
-/
theorem Triple.of_call [Bindings] {pre : RamState → Prop} {p : BitVec 64} {bytes : List UInt8}
    {len : Nat} (load : Bool) (hlen : bytes.length = len) (target : RamState → BitVec 64)
    (hpush : ∀ s, pre s → PushPre p len s)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → pre s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        callState (callFrom load t (BitVec.add p (BitVec.ofNat 64 len)))
          (BitVec.add p (BitVec.ofNat 64 len)) (target s)))) :
    Triple pre (codeRange p bytes) (Effect.post (callEffect target (p + BitVec.ofNat 64 len))) :=
  Triple.of_effect (fun s hpre => pushEffect_avoids hlen _ _ (hpush s hpre))
    (StepEffect.of_call load target hpush hstep)

/-! ### `call rel32` (`E8`) -/

/-- The step behind `call_rel32_triple`: from a ready state with the instruction in memory and the
precondition, one `step` reaches a ready state with the effect `callEffect`. -/
theorem call_rel32_effect_step [Bindings] (p : BitVec 64) (disp : BitVec 32)
    (htarget : (branchTarget p 5 (disp.signExtend 64)).toNat < 2^32) :
    StepEffect (PushPre p 5) (codeRange p (encodeCallRel32 disp))
      (callEffect (fun _ => branchTarget p 5 (disp.signExtend 64))
        (p + BitVec.ofNat 64 5)) :=
  StepEffect.of_call false _ (fun _ h => h) fun s h hcode hpre => by
    have hp := hpre.rip
    subst hp
    exact call_rel32_step s h disp hcode.bytesAt (hcode.low (by simp [encodeCallRel32])
      (by simp [encodeCallRel32])) htarget hpre.write

/--
The triple for `call rel32` (`E8`, displacement `disp`) at `p`: push `p + 5`, jump to
`branchTarget p 5 (sext disp)` = `p + 5 + sext disp` (below 4 GiB, `htarget`).
-/
theorem call_rel32_triple [Bindings] (p : BitVec 64) (disp : BitVec 32)
    (htarget : (branchTarget p 5 (disp.signExtend 64)).toNat < 2^32) :
    Triple (PushPre p 5) (codeRange p (encodeCallRel32 disp))
      (Effect.post (callEffect (fun _ => branchTarget p 5 (disp.signExtend 64))
        (p + BitVec.ofNat 64 5))) :=
  Triple.of_effect (fun _ hpre => pushEffect_avoids (by simp [encodeCallRel32]) _ _ hpre)
    (call_rel32_effect_step p disp htarget)

/-! ### `call r64` (`FF /2`, register) -/

/-- The step behind `call_r64_triple_of_bytes`: from a ready state with the instruction in memory
and the precondition, one `step` reaches a ready state with the effect `callEffect`. -/
theorem call_r64_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    let target := fun s => (Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 64).read s
    StepEffect (CallPre p 2 target) (codeRange p [0xFF, modrm])
      (callEffect target (p + BitVec.ofNat 64 2)) := by
  intro target
  refine StepEffect.of_call false _ (fun _ h => h.1) fun s h hcode ⟨hpre, htarget⟩ => ?_
  have hp := hpre.rip
  subst hp
  exact call_r64_step s h [] (by simp) (by simp) rfl rfl rfl modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)) htarget hpre.write

/--
The triple for `call r64` (`FF /2`, `mod = 3`, no prefix) at `p`, for registers 0–7: push
`p + 2`, jump to the value of register `modrm & 7` (below 4 GiB).
-/
theorem call_r64_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    let target := fun s => (Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 64).read s
    Triple (CallPre p 2 target) (codeRange p [0xFF, modrm])
      (Effect.post (callEffect target (p + BitVec.ofNat 64 2))) := by
  intro target
  exact Triple.of_effect (fun _ hpre => pushEffect_avoids rfl _ _ hpre.1)
    (call_r64_effect_step p modrm hmod hreg)

/-- The step behind `call_r64_rex_triple_of_bytes`: from a ready state with the instruction in
memory and the precondition, one `step` reaches a ready state with the effect `callEffect`. -/
theorem call_r64_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    let target := fun s =>
      (Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 64).read s
    StepEffect (CallPre p 3 target) (codeRange p [rex, 0xFF, modrm])
      (callEffect target (p + BitVec.ofNat 64 3)) := by
  intro target
  refine StepEffect.of_call false _ (fun _ h => h.1) fun s h hcode ⟨hpre, htarget⟩ => ?_
  have hp := hpre.rip
  subst hp
  have hstep := call_r64_step s h [rex] (by simpa using hrex.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hrex]; rfl) (by rw [scanContext_rex _ _ hrex]; rfl)
    (by rw [scanContext_rex _ _ hrex]; rfl) modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)) (by rw [scanContext_rex _ _ hrex]; exact htarget) hpre.write
  simp only [scanContext_rex _ _ hrex] at hstep
  exact hstep

/--
The triple for `call r64` (`REX FF /2`, `mod = 3`) at `p`, for any REX byte and any of the 16
registers: push `p + 3`, jump to the value of register `modrm & 7` extended by REX.B (for
example `41 FF D5`, `call r13`).
-/
theorem call_r64_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2) :
    let target := fun s =>
      (Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 64).read s
    Triple (CallPre p 3 target) (codeRange p [rex, 0xFF, modrm])
      (Effect.post (callEffect target (p + BitVec.ofNat 64 3))) := by
  intro target
  exact Triple.of_effect (fun _ hpre => pushEffect_avoids rfl _ _ hpre.1)
    (call_r64_rex_effect_step p rex modrm hrex hmod hreg)

/-- The triple for `call r` on the 64-bit register numbered `r` (0–15) at `p`, in the encoding
`encodeCallR64 r` (2 or 3 bytes): push `p + len`, jump to the register's value. -/
theorem call_r64_triple [Bindings] (p : BitVec 64) (r : BitVec 4) :
    let target := fun s => (Operand.reg (r.setWidth 5) : Operand 64).read s
    Triple (CallPre p (encodeCallR64 r).length target) (codeRange p (encodeCallR64 r))
      (Effect.post (callEffect target (p + BitVec.ofNat 64 (encodeCallR64 r).length))) := by
  rcases encodeCallR64_spec r with ⟨modrm, hbytes, hmod, hreg, hr⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hr⟩
  · rw [hbytes, ← hr]
    exact call_r64_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hr]
    exact call_r64_rex_triple_of_bytes p rex modrm hrex hmod hreg

/-! ### `call [mem]` (`FF /2`, memory) -/

/-- The length of `encodeCallM64 am`. -/
abbrev callMemLen (am : AddrMode) : Nat := 2 + am.tail.length

/-- The pointer `call qword [am]` at `p` reads, in state `s`. -/
abbrev callMemPtr (p : BitVec 64) (am : AddrMode) (s : RamState) : BitVec 64 :=
  (Operand.mem (am.addr s (p + BitVec.ofNat 64 (callMemLen am))) : Operand 64).read s

/-- The precondition of `call qword [am]` at `p`: `CallPre` with the pointer as target, and the
pointer's 8 bytes readable. -/
abbrev CallMemPre (p : BitVec 64) (am : AddrMode) (s : RamState) : Prop :=
  CallPre p (callMemLen am) (callMemPtr p am) s ∧
    MemReadable s (am.addr s (p + BitVec.ofNat 64 (callMemLen am))) 8

/-- The step behind `call_m64_triple`: from a ready state with the instruction in memory and the
precondition, one `step` reaches a ready state with the effect `callEffect`. -/
theorem call_m64_effect_step [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (CallMemPre p am) (codeRange p (encodeCallM64 am))
      (callEffect (callMemPtr p am) (p + BitVec.ofNat 64 (callMemLen am))) := by
  refine StepEffect.of_call true _ (fun _ h => h.1.1)
    fun s h hcode ⟨⟨hpre, htarget⟩, hread⟩ => ?_
  have hp := hpre.rip
  subst hp
  have h5 := am.tail_length_le
  have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
    have := hcode.low (by simp [encodeCallM64]) (by simp [encodeCallM64]; omega)
    simp only [encodeCallM64, List.length_cons] at this
    omega
  exact call_m64_step s h [] (by simp) (by simp) rfl rfl rfl am hv
    (AddrContext.legacy _ am hx hb) hcode.bytesAt hlow hread htarget hpre.write

/--
The triple for `call qword [am]` (`FF /2`, `mod ≠ 3`, no prefix) at `p`, for any addressing shape
`am` that needs no REX bit (for example `FF 15 d32`, `call [rip + d32]`): read the 8-byte pointer at
`am.addr s (p + len)`, push `p + len`, jump to the pointer.
-/
theorem call_m64_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (CallMemPre p am) (codeRange p (encodeCallM64 am))
      (Effect.post (callEffect (callMemPtr p am) (p + BitVec.ofNat 64 (callMemLen am)))) :=
  Triple.of_effect
    (fun _ hpre => pushEffect_avoids (by simp [encodeCallM64, callMemLen]; omega) _ _ hpre.1.1)
    (call_m64_effect_step p am hv hx hb)

/-- `call [rip + d32]` (`FF 15 d32`) at `p`: the pointer is at `p + 6 + sext d`. -/
theorem call_m64_rip_triple [Bindings] (p : BitVec 64) (d : BitVec 32) :
    Triple (CallMemPre p (.rip d)) (codeRange p (encodeCallM64 (.rip d)))
      (Effect.post (callEffect (callMemPtr p (.rip d)) (p + BitVec.ofNat 64 6))) :=
  call_m64_triple p (.rip d) trivial rfl rfl

/-! ### `call [mem]` through an FS/GS segment override -/

/-- The length of `r.prefixByte :: encodeCallM64 am`. -/
abbrev callMemSegLen (am : AddrMode) : Nat := 3 + am.tail.length

/-- The pointer `call qword fs:[am]` (or `gs:`) at `p` reads, in state `s`, for the segment base
`base`. -/
abbrev callMemSegPtr (p base : BitVec 64) (am : AddrMode) (s : RamState) : BitVec 64 :=
  (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 (callMemSegLen am))) : Operand 64).read s

/-- The precondition of `call qword fs:[am]` (or `gs:`, `r`) at `p`: `CallPre` with the pointer as
target, the segment ready with base `base`, and the pointer's 8 bytes at `base + am.addr …`
readable. The return address is pushed on SS, which takes no override. -/
abbrev CallMemSegPre (p : BitVec 64) (r : SegReg) (base : BitVec 64) (am : AddrMode)
    (s : RamState) : Prop :=
  CallPre p (callMemSegLen am) (callMemSegPtr p base am) s ∧ r.Ready base s ∧
    MemReadable s (base + am.addr s (p + BitVec.ofNat 64 (callMemSegLen am))) 8

/-- The step behind `call_m64_seg_triple`. -/
theorem call_m64_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (CallMemSegPre p r base am) (codeRange p (r.prefixByte :: encodeCallM64 am))
      (callEffect (callMemSegPtr p base am) (p + BitVec.ofNat 64 (callMemSegLen am))) := by
  refine StepEffect.of_call true _ (fun _ h => h.1.1)
    fun s h hcode ⟨⟨hpre, htarget⟩, ⟨hseg, hbase⟩, hread⟩ => ?_
  have hp := hpre.rip
  subst hp hbase
  have h5 := am.tail_length_le
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := hcode.low (by simp [encodeCallM64]) (by simp [encodeCallM64]; omega)
    simp only [encodeCallM64, List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) :=
    scanContext_seg_cons _ _ r [] noSegPrefix_nil
  have hstep := call_m64_seg_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg) hcode.bytesAt hlow
    (by rw [hsc, segAddr_withSeg]; exact hread) (by rw [hsc, segAddr_withSeg]; exact htarget)
    hpre.write
  simp only [hsc, segAddr_withSeg] at hstep
  exact hstep

/--
The triple for `call qword fs:[am]` or `gs:[am]` (`64` or `65`, then `FF /2`, `mod ≠ 3`) at `p`,
for any addressing shape `am` that needs no REX bit: read the 8-byte pointer at
`base + am.addr s (p + len)` (`base` the segment's base), push `p + len`, jump to the pointer.
-/
theorem call_m64_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (CallMemSegPre p r base am) (codeRange p (r.prefixByte :: encodeCallM64 am))
      (Effect.post (callEffect (callMemSegPtr p base am)
        (p + BitVec.ofNat 64 (callMemSegLen am)))) :=
  Triple.of_effect
    (fun _ hpre => pushEffect_avoids (by simp [encodeCallM64, callMemSegLen]; omega) _ _
      hpre.1.1)
    (call_m64_seg_effect_step p r base am hv hx hb)

/-! ### `call [mem]` at address size 32 (`67`) -/

/-- The length of `0x67 :: encodeCallM64 am`. -/
abbrev callMemA32Len (am : AddrMode) : Nat := 3 + am.tail.length

/-- The pointer `call qword [am]` behind `67` at `p` reads, in state `s`: the 8 bytes at the
operand's 32-bit address (`AddrMode.addr32`). -/
abbrev callMemA32Ptr (p : BitVec 64) (am : AddrMode) (s : RamState) : BitVec 64 :=
  (Operand.mem (am.addr32 s (p + BitVec.ofNat 64 (callMemA32Len am))) : Operand 64).read s

/-- The precondition of `call qword [am]` behind `67` at `p`: `CallPre` with the pointer as target,
and the pointer's 8 bytes at `am.addr32 …` readable. -/
abbrev CallMemA32Pre (p : BitVec 64) (am : AddrMode) (s : RamState) : Prop :=
  CallPre p (callMemA32Len am) (callMemA32Ptr p am) s ∧
    MemReadable s (am.addr32 s (p + BitVec.ofNat 64 (callMemA32Len am))) 8

/-- The step behind `call_m64_a32_triple`. -/
theorem call_m64_a32_effect_step [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (CallMemA32Pre p am) (codeRange p (0x67 :: encodeCallM64 am))
      (callEffect (callMemA32Ptr p am) (p + BitVec.ofNat 64 (callMemA32Len am))) := by
  refine StepEffect.of_call true _ (fun _ h => h.1.1)
    fun s h hcode ⟨⟨hpre, htarget⟩, hread⟩ => ?_
  have hp := hpre.rip
  subst hp
  have h5 := am.tail_length_le
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := hcode.low (by simp [encodeCallM64]) (by simp [encodeCallM64]; omega)
    simp only [encodeCallM64, List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] = withAsz (scanContext s.DS (PrefixSegments.ofState s) []) :=
    scanContext_asz_cons _ _ []
  have hstep := call_m64_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz) hcode.bytesAt hlow
    (by rw [hsc]; exact hread) (by rw [hsc]; exact htarget) hpre.write
  simp only [hsc] at hstep
  exact hstep

/--
The triple for `call qword [am]` behind `67` (`67 FF /2`, `mod ≠ 3`) at `p`, for any addressing
shape `am` that needs no REX bit: read the 8-byte pointer at `am.addr32 s (p + len)`, push
`p + len`, jump to the pointer.
-/
theorem call_m64_a32_triple [Bindings] (p : BitVec 64) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (CallMemA32Pre p am) (codeRange p (0x67 :: encodeCallM64 am))
      (Effect.post (callEffect (callMemA32Ptr p am) (p + BitVec.ofNat 64 (callMemA32Len am)))) :=
  Triple.of_effect
    (fun _ hpre => pushEffect_avoids (by simp [encodeCallM64, callMemA32Len]; omega) _ _
      hpre.1.1)
    (call_m64_a32_effect_step p am hv hx hb)

/-! ### `ret` (`C3`) -/

/-- The step behind `ret_triple`: from a ready state with the instruction in memory and the
precondition, one `step` reaches a ready state with the effect `retEffect`. -/
theorem ret_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (RetPre p) (codeRange p [0xC3]) retEffect := by
  rintro s h hcode ⟨hpre, htarget⟩
  have hp := hpre.rip
  subst hp
  exact ⟨_, ret_step s h hcode.bytesAt (hcode.low (by simp) (by simp)) hpre.read htarget,
    ReadyToStep.afterStep_ret h _ _,
    ⟨afterStep_ret_rip _ _, Operand.read_afterStep_ret_rsp _ _ _, trivial,
      AgreesExcept.afterStep_ret _ _ _⟩⟩

/-- The triple for `ret` (`C3`) at `p`: RIP := the 8 bytes at RSP, RSP := RSP + 8. -/
theorem ret_triple [Bindings] (p : BitVec 64) :
    Triple (RetPre p) (codeRange p [0xC3]) (Effect.post retEffect) :=
  Triple.of_effect (fun s _ =>
    Effect.avoids_of_components_reg_rip (retEffect_components s) _)
    (ret_effect_step p)
attribute [x86_compose] retEffect

@[x86_local] theorem retEffect_local :
    Effect.Local retEffect := by
  effect_local [retEffect, stackTop, stackPtr]

@[x86_compose, x86_pre_simp] theorem stackTop_eq_read (t : RamState) :
    stackTop t = (Operand.mem ((Operand.reg 4 : Operand 64).read t) : Operand 64).read t := by
  simp [stackTop, stackPtr]

end X86Proofs
