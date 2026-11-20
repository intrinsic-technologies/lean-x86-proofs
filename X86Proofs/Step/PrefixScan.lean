import X86Proofs.Step.ReadyToStep
import X86Proofs.Step.Prefix
import X86Proofs.Step.Completion

/-!
# The prefix scan: legacy and REX prefixes and the `0F` escape

This file proves the prefix scan once for a whole family: any list `pre` of prefix bytes, each a REX
byte (`40`–`4F`), `66` (operand size), `2E` (CS segment), `F3` (REP/REPE), `F2` (REPNE), `64` (FS
segment), `65` (GS segment), `F0` (LOCK, `lock_prefix_present`) or `67` (address size,
`asz_prefix_present`), followed by either a one-byte legacy opcode or the `0F` escape and a second
opcode byte. The context the decoder gets is `scanContext seg segs pre`: the default 64-bit context
with each prefix applied in order (`prefixUpdate`), and the operand and address sizes `Operand_Size`
and `Address_Size` compute from it (`scanOperandSize`, `scanAddressSize`: 32 after `67`, else 64).
`segs` are the segment registers a segment prefix selects (`PrefixSegments`; `(PrefixSegments.ofState s)` for the
state `s`): `64` and `65` make FS or GS the operand's segment (`seg_prefix_present`, the only
segment overrides of 64-bit mode; `2E` changes nothing but the REX bits).

lean-x86's `Fetch_And_Execute` scans with `Decode_Prefixes`, which runs the loop
`Decode_Legacy_Prefixes` (one `Decode_REX_Prefix`, or `Decode_Legacy_Prefix` and `Clear_REX_Prefix`,
per byte), sets the sizes and asks `Decode_Legacy_Map` for the opcode map:

- `decodeLegacyPrefixes_run`: the loop scans `pre` and the opcode byte (`pre.length + 1` fetches).
- `decodePrefixes_run`: `Decode_Prefixes` returns `scanContext`, and the map and decoder address
  `Decode_Legacy_Map` gives (`decodeLegacyMap_run_legacy0` for a one-byte opcode;
  `decodeLegacyMap_run_legacy1` for `0F`: one more fetch, the second opcode byte).
- `fetchAndExecute_scan_legacy0_of_fetchReady`, `fetchAndExecute_scan_legacy1_of_fetchReady`:
  `Fetch_And_Execute` then runs `Decode_Legacy_0` at the opcode, or `Decode_Legacy_1` at the second
  opcode byte, and the REP completion cleanup (`completeDecoded`); `step_scan_legacy0`,
  `step_scan_legacy1`: the step wrappers, as `step_rex_legacy0`.

It is the one file that unfolds `Fetch_And_Execute`, `Decode_Prefixes`, `Decode_Legacy_Prefixes`,
`Decode_Legacy_Prefix`, `Decode_Segment_Prefix`, `Decode_Legacy_Map`, `Initial_Instruction_Context`,
`Fetch_Extended_Prefix_Bytes` and `Operand_Size`; the fixed-shape fetch lemmas of
`Step/LegacyStep.lean` (no prefix, REX, `F3`, `F3` + REX) are instances of
`fetchAndExecute_scan_legacy0`.

Common compiled shapes are instances: `66 C7` and `66 90` (`pre = [66]`), `0F xx`
(`pre = []`), `41 0F 10` (`pre = [rex]`), `66 0F 1F`, `66 2E 0F 1F`, `66 66 66 2E 0F 1F` and
`66 66 66 66 2E 0F 1F` (multi-byte NOPs). `scanContext` reduces by `rfl` on a concrete prefix list;
`scanContext_nil`, `scanContext_rex`, `scanContext_66`, `scanContext_f2`, … name the results, and
`scanContext_seg_present`, `scanContext_segment` what a trailing run of prefixes after an FS/GS
prefix leaves of it; `scanContext_seg_cons`: an FS/GS prefix in front of prefixes that are not
segment prefixes (`NoSegPrefix`) gives their context with the override (`withSeg`);
`scanContext_lock_cons`: a LOCK prefix (`F0`) in front of any prefixes gives their context with
`lock_prefix_present` set (`withLock`); `scanContext_asz_cons`: an address-size prefix (`67`) in
front of any prefixes gives their context at address size 32 (`withAsz`).

The loop is handled once (`partialSpecM_loop_scan_run`, by induction on the prefixes) for an abstract loop
body; `decodeLegacyPrefixes_run` instantiates it with `Decode_Legacy_Prefixes`'s body and proves the
body's two behaviours (a prefix byte: update the context and continue; any other byte: stop) for a
symbolic context.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- A byte the scan lemmas cover as a prefix: REX (`40`–`4F`), `66`, `2E`, `F3`, `64`, `65`,
`F0` (LOCK), `F2` (REPNE) or `67` (address size). -/
def ScanPrefix (p : UInt8) : Prop :=
  RexPrefix p.toBitVec ∨ p = 0x66 ∨ p = 0x2E ∨ p = 0xF3 ∨ p = 0x64 ∨ p = 0x65 ∨ p = 0xF0 ∨
    p = 0xF2 ∨ p = 0x67

/-- The segment registers the scan's segment prefixes select: FS (`64`), GS (`65`). -/
structure PrefixSegments where
  fs : Segment
  gs : Segment

/-- The segment registers of `s` a segment prefix selects (FS, GS). -/
def PrefixSegments.ofState {σ : Type} (s : X86.State σ) : PrefixSegments :=
  ⟨s.FS, s.GS⟩

/-- A legacy prefix clears the REX bits: a REX prefix only counts if it is the last prefix. -/
def clearRex (ctx : Instruction_Context) : Instruction_Context :=
  {ctx with rex_prefix_present := false, rex_w := 0, rex_r3 := 0, rex_x3 := 0, rex_b3 := 0}

/--
What the prefix scan does to the decode context on the prefix byte `p` (one of `ScanPrefix`), in
64-bit mode: `66` sets `osz_prefix_present`; `2E` (CS) is not a segment override in 64-bit mode
and leaves the segment and `seg_prefix_present` alone, so it keeps an earlier FS or GS override
(lean-x86's `Decode_Segment_Prefix`); `F3` sets
`rep_prefix = 243` and `F2` sets `rep_prefix = 242` (so the last of `F2`/`F3` wins, as in
lean-x86); `64` and `65` set the segment to FS or GS (`segs.fs`, `segs.gs`), a segment override
(`seg_prefix_present` becomes true), and clear `no_track_prefix`; `F0` sets
`lock_prefix_present`; `67` sets `asz_prefix_present` (the address size is set after the scan,
`scanAddressSize`); these eight clear the REX bits. A REX byte sets them.
-/
def prefixUpdate (segs : PrefixSegments) (ctx : Instruction_Context) (p : UInt8) :
    Instruction_Context :=
  if p = 0x66 then clearRex {ctx with osz_prefix_present := true}
  else if p = 0x2E then clearRex ctx
  else if p = 0xF3 then clearRex {ctx with rep_prefix := 243}
  else if p = 0x64 then
    clearRex {ctx with no_track_prefix := false, segment := segs.fs, seg_prefix_present := true}
  else if p = 0x65 then
    clearRex {ctx with no_track_prefix := false, segment := segs.gs, seg_prefix_present := true}
  else if p = 0xF0 then clearRex {ctx with lock_prefix_present := true}
  else if p = 0xF2 then clearRex {ctx with rep_prefix := 242}
  else if p = 0x67 then clearRex {ctx with asz_prefix_present := true}
  else
    {ctx with
      rex_prefix_present := true, rex_w := BitVec.extractLsb' 3 1 p.toBitVec,
      rex_r3 := rexR p.toBitVec, rex_x3 := BitVec.extractLsb' 1 1 p.toBitVec,
      rex_b3 := rexB p.toBitVec}

/-- `Operand_Size` in 64-bit mode without REX2/VEX/EVEX: 64 with REX.W, else 16 with `66`, else 32. -/
def scanOperandSize (ctx : Instruction_Context) : Int :=
  if ctx.rex_prefix_present then
    if ctx.rex_w == 0 then (if ctx.osz_prefix_present then 16 else 32) else 64
  else if ctx.osz_prefix_present then 16 else 32

/-- `Address_Size` in 64-bit mode: 32 with an address-size prefix (`67`), else 64. -/
def scanAddressSize (ctx : Instruction_Context) : Int :=
  if ctx.asz_prefix_present then 32 else 64

/--
The decode context after the prefixes `pre`: the default 64-bit context (`legacyContext seg`)
with each prefix applied in order (`segs`: the segment registers `64` and `65` select), and
the operand and address sizes they select.
-/
noncomputable def scanContext (seg : Segment) (segs : PrefixSegments) (pre : List UInt8) :
    Instruction_Context :=
  let ctx := pre.foldl (prefixUpdate segs) (legacyContext seg)
  {ctx with operand_size := scanOperandSize ctx, address_size := scanAddressSize ctx}

/-- The context facts the scan keeps: 64-bit mode, and no REX2, VEX or EVEX prefix. -/
def ScanInv (ctx : Instruction_Context) : Prop :=
  ctx.is_mode64 = true ∧ ctx.rex2_prefix_present = false ∧
    ctx.vex_prefix_present = false ∧ ctx.evex_prefix_present = false ∧ ctx.vex_pp = 0

theorem ScanInv.update {segs : PrefixSegments} {ctx : Instruction_Context} (h : ScanInv ctx)
    (p : UInt8) : ScanInv (X86Proofs.prefixUpdate segs ctx p) := by
  unfold X86Proofs.prefixUpdate
  repeat' split
  all_goals exact h

theorem ScanInv.foldl {segs : PrefixSegments} {ctx : Instruction_Context} (h : ScanInv ctx)
    (pre : List UInt8) : ScanInv (pre.foldl (prefixUpdate segs) ctx) := by
  induction pre generalizing ctx with
  | nil => exact h
  | cons p pre ih => exact ih (h.update p)

/-- Split `prefixUpdate` on the prefix byte `p` (its nine cases, the last one REX), closing each
case with `tac`. -/
local macro "prefix_cases " p:term:max " => " tac:tactic : tactic => `(tactic| (
  unfold prefixUpdate
  by_cases h66 : $p = 0x66
  · simp only [h66, ↓reduceIte] <;> $tac
  simp only [h66, ↓reduceIte]
  by_cases h2e : $p = 0x2E
  · simp only [h2e, ↓reduceIte] <;> $tac
  simp only [h2e, ↓reduceIte]
  by_cases hf3 : $p = 0xF3
  · simp only [hf3, ↓reduceIte] <;> $tac
  simp only [hf3, ↓reduceIte]
  by_cases h64 : $p = 0x64
  · simp only [h64, ↓reduceIte] <;> $tac
  simp only [h64, ↓reduceIte]
  by_cases h65 : $p = 0x65
  · simp only [h65, ↓reduceIte] <;> $tac
  simp only [h65, ↓reduceIte]
  by_cases hf0 : $p = 0xF0
  · simp only [hf0, ↓reduceIte] <;> $tac
  simp only [hf0, ↓reduceIte]
  by_cases hf2 : $p = 0xF2
  · simp only [hf2, ↓reduceIte] <;> $tac
  simp only [hf2, ↓reduceIte]
  by_cases h67 : $p = 0x67
  · simp only [h67, ↓reduceIte] <;> $tac
  simp only [h67, ↓reduceIte] <;> $tac))

theorem prefixUpdate_address_size (segs : PrefixSegments) (ctx : Instruction_Context) (p : UInt8)
    (a : Int) :
    prefixUpdate segs {ctx with address_size := a} p =
      {prefixUpdate segs ctx p with address_size := a} := by
  prefix_cases p => rfl

theorem foldl_prefixUpdate_address_size (segs : PrefixSegments) (pre : List UInt8)
    (ctx : Instruction_Context) (a : Int) :
    pre.foldl (prefixUpdate segs) {ctx with address_size := a} =
      {pre.foldl (prefixUpdate segs) ctx with address_size := a} := by
  induction pre generalizing ctx with
  | nil => rfl
  | cons p pre ih => simp only [List.foldl_cons, prefixUpdate_address_size, ih]

theorem foldl_prefixUpdate_address_size' (segs : PrefixSegments) (pre : List UInt8)
    (ctx : Instruction_Context) :
    (pre.foldl (prefixUpdate segs) ctx).address_size = ctx.address_size := by
  induction pre generalizing ctx with
  | nil => rfl
  | cons p pre ih =>
    rw [List.foldl_cons, ih]
    unfold prefixUpdate
    repeat' split
    all_goals rfl

/-- `Operand_Size` on a context the scan builds is `scanOperandSize`. -/
theorem operandSize_scan [X86.Machine.Bindings] (ctx : Instruction_Context) (h : ScanInv ctx)
    (s : RamState) (hmode : In64BitMode s) :
    (Operand_Size ctx).run s = (.ok (scanOperandSize ctx), s) := by
  unfold Operand_Size
  refine (specM_bind_run _ _ hmode).trans ?_
  obtain ⟨-, h3, h4, h5, h6⟩ := h
  unfold scanOperandSize
  cases hr : ctx.rex_prefix_present <;> cases ho : ctx.osz_prefix_present <;>
    simp [h3, h4, h5, h6, HOr.hOr, OrOp.or, strictOr] <;> (try split) <;> rfl

/-- `Address_Size` in 64-bit mode is `scanAddressSize`. -/
theorem addressSize_scan (ctx : Instruction_Context) (h : ctx.is_mode64 = true) (s : RamState) :
    (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run s =
      (.ok (scanAddressSize ctx), s) := by
  rw [addressSize_mode64_run ctx h]
  rfl

/-- The prefix-scan loop's state: the context, the last byte read, the offset, "saw a prefix". -/
abbrev ScanState := Instruction_Context × X86.Runtime.InitializedBits 8 × Int × Bool

/--
The prefix-scan loop, for an abstract loop body. If at offset `k < pre.length` the body updates
the context by `upd` with byte `pre[k]` and continues at offset `k + 1` (one more state step),
and at offset `pre.length` it stops with the opcode byte `op`, then the loop from offset 0 ends at
offset `pre.length` with the context `pre.foldl upd ctx`.
-/
theorem partialSpecM_loop_scan_run {exception σ : Type}
    (body : Unit → ScanState → X86.Runtime.PartialSpecM exception σ (ForInStep ScanState))
    (st : Nat → σ) (pre : List UInt8) (op : UInt8)
    (upd : Instruction_Context → UInt8 → Instruction_Context) (Inv : Instruction_Context → Prop)
    (hinv : ∀ c p, Inv c → Inv (upd c p))
    (hyield : ∀ c b (k : Nat) (hk : k < pre.length), Inv c →
      (body () (c, b, (k : Int), true)).run (st k) =
        some (.ok (.yield (upd c pre[k], .ofValue pre[k].toBitVec, ((k + 1 : Nat) : Int), true)),
          st (k + 1)))
    (hdone : ∀ c b, Inv c →
      (body () (c, b, (pre.length : Int), true)).run (st pre.length) =
        some (.ok (.done (c, .ofValue op.toBitVec, (pre.length : Int), false)), st (pre.length + 1)))
    (c : Instruction_Context) (b : X86.Runtime.InitializedBits 8) (hc : Inv c) :
    (X86.Runtime.PartialLoop.forIn (c, b, (0 : Int), true) body).run (st 0) =
      some (.ok (pre.foldl upd c, .ofValue op.toBitVec, (pre.length : Int), false),
        st (pre.length + 1)) := by
  suffices h : ∀ n j c b, j + n = pre.length → Inv c →
      (X86.Runtime.PartialLoop.forIn (c, b, (j : Int), true) body).run (st j) =
        some (.ok ((pre.drop j).foldl upd c, .ofValue op.toBitVec, (pre.length : Int), false),
          st (pre.length + 1)) from
    h pre.length 0 c b (Nat.zero_add _) hc
  intro n
  induction n with
  | zero =>
    intro j c b hj hc
    subst hj
    simp only [List.drop_length, List.foldl_nil]
    exact partialSpecM_loop_done_run _ _ _ (hdone c b hc)
  | succ n ih =>
    intro j c b hj hc
    have hk : j < pre.length := by omega
    refine partialSpecM_loop_yield_run _ _ _ _ (hyield c b j hk hc) ?_
    rw [List.drop_eq_getElem_cons hk, List.foldl_cons]
    exact ih (j + 1) _ _ (by omega) (hinv c _ hc)

theorem initializedBitsRead_ofValue_run (byte : BitVec 8) (s : RamState) :
    (X86.Runtime.InitializedBits.read (X86.Runtime.InitializedBits.ofValue (size := 8) byte) :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 8)).run s = some (.ok byte, s) := by
  simp [x86_runtime, pure, ExceptT.pure, StateT.pure, ExceptT.run, ExceptT.mk]

/-- A byte that ends the prefix scan without a VEX/EVEX/REX2 escape: `0F` or a `LegacyOpcode`. -/
def ScanOpcode (byte : BitVec 8) : Prop :=
  (BitVec.and byte 240#8 == 64#8) = false ∧
  ∀ n : BitVec 8, n ∈ [38,46,54,62,100,101,102,103,240,242,243,98,196,197,213] → (byte == n) = false

theorem LegacyOpcode.scanOpcode {byte : BitVec 8} (h : LegacyOpcode byte) : ScanOpcode byte :=
  ⟨h.1, fun n hn => h.2 n (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
    rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h])⟩

theorem scanOpcode_0F : ScanOpcode 0x0F :=
  ⟨by decide, by decide⟩

theorem scanByte_noExtendedPrefix [instBindings : X86.Machine.Bindings]
    (byte : BitVec 8) (hb : ScanOpcode byte) (s : RamState) (ip : BitVec 64) :
    (Fetch_Extended_Prefix_Bytes byte ip true).run s = (.ok (false,0,0,0), s) := by
  have h98 := hb.2 98 (by decide)
  have h196 := hb.2 196 (by decide)
  have h197 := hb.2 197 (by decide)
  have h213 := hb.2 213 (by decide)
  unfold Fetch_Extended_Prefix_Bytes
  simp only [h98, h196, h197, h213, Bool.false_eq_true, ↓reduceIte,
    HAnd.hAnd, AndOp.and, strictAnd, Bool.false_and]
  rfl

/-- `Initial_Instruction_Context` in 64-bit mode: the default context with the state's DS, before
the scan sets its address size. -/
theorem initialInstructionContext_run [X86.Machine.Bindings] (s : RamState) (hf : FetchReady s) :
    Initial_Instruction_Context.run s =
      (.ok {legacyContext s.DS with address_size := 32, operand_size := 32}, s) := by
  have hg : (get : X86.Runtime.SpecM X86.Exception RamState RamState).run s = (.ok s, s) := rfl
  unfold Initial_Instruction_Context
  refine (specM_bind_run _ _ hg).trans ?_
  refine (specM_bind_run _ _ (currentMode_run s hf.cr0 hf.efer.lma)).trans ?_
  refine (specM_bind_run _ _ (in64BitMode_of_userCodeSegment hf.cs hf.efer.lma)).trans ?_
  rfl

/-- A byte that ends the scan (`ScanOpcode`) is not a legacy prefix: `Decode_Legacy_Prefix` (and
the `Decode_Segment_Prefix` it starts with) answers `false` and leaves the context alone. -/
theorem decodeLegacyPrefix_run_of_scanOpcode (byte : BitVec 8) (hb : ScanOpcode byte)
    (c : Instruction_Context) (s : RamState) :
    (Decode_Legacy_Prefix byte c).run s = (.ok (false, c), s) := by
  have hn := hb.2
  unfold Decode_Legacy_Prefix Decode_Segment_Prefix
  simp only [hn 38 (by decide), hn 46 (by decide), hn 54 (by decide), hn 62 (by decide),
    hn 100 (by decide), hn 101 (by decide), hn 102 (by decide), hn 103 (by decide),
    hn 240 (by decide), hn 242 (by decide), hn 243 (by decide), Bool.false_eq_true, ↓reduceIte]
  rfl

/--
The legacy-prefix scan for `pre ++ op :: rest` at RIP, below 4 GiB: `pre` is a list of `ScanPrefix`
bytes and `op` ends the scan (`ScanOpcode`: a one-byte opcode or `0F`). `Decode_Legacy_Prefixes`
fetches the `pre.length + 1` bytes and returns the initial context with each prefix applied in
order (`prefixUpdate`), the byte `op` and the offset `pre.length`.
-/
theorem decodeLegacyPrefixes_run [instBindings : X86.Machine.Bindings]
    (s : RamState) (hf : FetchReady s) (pre : List UInt8) (op : UInt8) (rest : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hop : ScanOpcode op.toBitVec) (hlen : pre.length < 15)
    (hcode : BytesAt s s.RIP (pre ++ op :: rest))
    (hlow : s.RIP.toNat + (pre ++ op :: rest).length ≤ 2^32) :
    (Decode_Legacy_Prefixes s.RIP).run s =
      some (.ok (pre.foldl (prefixUpdate (PrefixSegments.ofState s))
          {legacyContext s.DS with address_size := 32, operand_size := 32},
        op.toBitVec, (pre.length : Int)), afterFetches s (pre.length + 1)) := by
  have hfetch (k : Nat) (hk : k < pre.length) :
      (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 k)) 8).run (afterFetches s k) =
        (.ok pre[k].toBitVec, afterFetches s (k + 1)) := by
    have := memFetch_run_of_bytesAt s k hf hcode hlow k (by simp; omega) (by omega)
    rwa [List.getElem_append_left hk] at this
  have hfetchOp : (Mem_Fetch (BitVec.add s.RIP (BitVec.ofNat 64 pre.length)) 8).run
      (afterFetches s pre.length) = (.ok op.toBitVec, afterFetches s (pre.length + 1)) := by
    have := memFetch_run_of_bytesAt s pre.length hf hcode hlow pre.length (by simp) hlen
    simpa using this
  have hinv0 : ScanInv ({legacyContext s.DS with address_size := 32, operand_size := 32}) :=
    ⟨rfl, rfl, rfl, rfl, rfl⟩
  unfold Decode_Legacy_Prefixes
  refine (partialSpecM_bind_run _ _
    (partialSpecM_liftTotal_run _ (initialInstructionContext_run s hf))).trans ?_
  refine (partialSpecM_bind_run (X86.Runtime.PartialLoop.forIn _ ?body) _ (s := s)
    (t := afterFetches s (pre.length + 1))
    (value := (pre.foldl (prefixUpdate (PrefixSegments.ofState s))
        {legacyContext s.DS with address_size := 32, operand_size := 32},
      X86.Runtime.InitializedBits.ofValue (size := 8) op.toBitVec, (pre.length : Int), false)) ?loop).trans ?_
  case loop =>
    refine Eq.trans ?_ (partialSpecM_loop_scan_run ?body (afterFetches s) pre op (prefixUpdate (PrefixSegments.ofState s)) ScanInv
      (fun c p hc => hc.update p) ?yield ?done _ (X86.Runtime.InitializedBits.empty 8) hinv0)
    · rw [afterFetches_zero]
    case yield =>
      intro c b k hk hc
      refine (partialSpecM_bind_run (liftM (Std.Bits.Add_int (n := 64) s.RIP k)) _
        (value := BitVec.add s.RIP (BitVec.ofNat 64 k)) rfl).trans ?_
      refine (partialSpecM_bind_run _ _ (partialSpecM_liftTotal_run _ (hfetch k hk))).trans ?_
      have hp := hpre _ (List.getElem_mem hk)
      generalize pre[k] = p at hp ⊢
      obtain ⟨h1, -⟩ := hc
      cases c
      cases h1
      rcases hp with hp | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [RexPrefix, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
          (obtain rfl : p = _ := UInt8.toBitVec_inj.mp h; rfl)
      all_goals rfl
    case done =>
      intro c b hc
      refine (partialSpecM_bind_run (liftM (Std.Bits.Add_int (n := 64) s.RIP pre.length)) _
        (value := BitVec.add s.RIP (BitVec.ofNat 64 pre.length)) rfl).trans ?_
      refine (partialSpecM_bind_run _ _ (partialSpecM_liftTotal_run _ hfetchOp)).trans ?_
      have hr := initializedBitsRead_ofValue_run op.toBitVec (afterFetches s (pre.length + 1))
      have hc' : (do
          let b ← (X86.Runtime.InitializedBits.read
            (X86.Runtime.InitializedBits.ofValue (size := 8) op.toBitVec) :
            X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 8))
          pure ((BitVec.and b 240#8) == 64#8)).run (afterFetches s (pre.length + 1)) =
            some (.ok false, afterFetches s (pre.length + 1)) := by
        refine (partialSpecM_bind_run _ _ hr).trans ?_
        exact congrArg (fun b => some ((Except.ok b : Except (X86.Runtime.Error X86.Exception) Bool),
          afterFetches s (pre.length + 1))) hop.1
      refine (partialSpecM_bind_run _ _ hc').trans ?_
      simp only [Bool.and_false, HAnd.hAnd, AndOp.and, strictAnd, Bool.false_eq_true, ↓reduceIte]
      refine (partialSpecM_bind_run _ _ hr).trans ?_
      refine (partialSpecM_bind_run _ _ (partialSpecM_liftTotal_run _
        (decodeLegacyPrefix_run_of_scanOpcode op.toBitVec hop c _))).trans ?_
      rfl
  exact (partialSpecM_bind_run _ _ (initializedBitsRead_ofValue_run op.toBitVec _)).trans rfl

/-- `Decode_Legacy_Map` at a one-byte opcode (not `0F`): the one-byte map, at the opcode. -/
theorem decodeLegacyMap_run_legacy0 [X86.Machine.Bindings] (ip : BitVec 64) (byte : BitVec 8)
    (h15 : (byte == 15) = false) (s : RamState) :
    (Decode_Legacy_Map ip byte).run s = (.ok (.Map_Legacy_0, ip), s) := by
  unfold Decode_Legacy_Map
  simp only [h15, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- `Decode_Legacy_Map` at the `0F` escape, followed by a byte `op2` other than `38` and `3A` (the
three-byte maps): one more fetch, then the two-byte map at `op2`. -/
theorem decodeLegacyMap_run_legacy1 [X86.Machine.Bindings] (ip : BitVec 64) (op2 : BitVec 8)
    (s t : RamState) (hfetch : (Mem_Fetch (BitVec.add ip 1#64) 8).run s = (.ok op2, t))
    (h56 : (op2 == 56) = false) (h58 : (op2 == 58) = false) :
    (Decode_Legacy_Map ip 15).run s = (.ok (.Map_Legacy_1, BitVec.add ip 1#64), t) := by
  unfold Decode_Legacy_Map
  simp only [beq_self_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _
    (value := BitVec.add ip 1#64) rfl).trans ?_
  refine (specM_bind_run _ _ hfetch).trans ?_
  simp only [h56, h58, Bool.false_eq_true, ↓reduceIte]
  rfl

/--
`Decode_Prefixes` for `pre ++ op :: rest` at RIP (as `decodeLegacyPrefixes_run`), given what
`Decode_Legacy_Map` answers at the opcode byte (`hmap`: the opcode map and the address the map's
decoder starts at). It returns the context `scanContext s.DS (PrefixSegments.ofState s) pre`, that
map and address, and the byte `op`.
-/
theorem decodePrefixes_run [instBindings : X86.Machine.Bindings]
    (s t : RamState) (hf : FetchReady s) (pre : List UInt8) (op : UInt8) (rest : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hop : ScanOpcode op.toBitVec) (hlen : pre.length < 15)
    (hcode : BytesAt s s.RIP (pre ++ op :: rest))
    (hlow : s.RIP.toNat + (pre ++ op :: rest).length ≤ 2^32)
    (map : Instruction_Map) (opcodeIp : BitVec 64)
    (hmap : (Decode_Legacy_Map (BitVec.add s.RIP (BitVec.ofNat 64 pre.length)) op.toBitVec).run
      (afterFetches s (pre.length + 1)) = (.ok (map, opcodeIp), t)) :
    (Decode_Prefixes s.RIP).run s =
      some (.ok (scanContext s.DS (PrefixSegments.ofState s) pre, map, opcodeIp, op.toBitVec), t) := by
  have hcs := hf.cs
  have hlma := hf.efer.lma
  unfold Decode_Prefixes
  refine (partialSpecM_bind_run _ _
    (decodeLegacyPrefixes_run s hf pre op rest hpre hop hlen hcode hlow)).trans ?_
  -- After the loop: the context is `scanContext` before its sizes are set.
  have hval : pre.foldl (prefixUpdate (PrefixSegments.ofState s))
      {legacyContext s.DS with address_size := 32, operand_size := 32} =
      {pre.foldl (prefixUpdate (PrefixSegments.ofState s)) (legacyContext s.DS) with address_size := 32} :=
    foldl_prefixUpdate_address_size (PrefixSegments.ofState s) pre (legacyContext s.DS) 32
  rw [hval]
  change _ = some (Except.ok ({pre.foldl (prefixUpdate (PrefixSegments.ofState s)) (legacyContext s.DS) with
      operand_size := scanOperandSize (pre.foldl (prefixUpdate (PrefixSegments.ofState s)) (legacyContext s.DS)),
      address_size := scanAddressSize (pre.foldl (prefixUpdate (PrefixSegments.ofState s)) (legacyContext s.DS))},
    map, opcodeIp, op.toBitVec), t)
  have hinv : ScanInv (pre.foldl (prefixUpdate (PrefixSegments.ofState s)) (legacyContext s.DS)) :=
    ScanInv.foldl ⟨rfl, rfl, rfl, rfl, rfl⟩ pre
  have haddr := foldl_prefixUpdate_address_size' (PrefixSegments.ofState s) pre (legacyContext s.DS)
  generalize pre.foldl (prefixUpdate (PrefixSegments.ofState s)) (legacyContext s.DS) = c at hinv haddr ⊢
  have hasz : ∀ v : RamState, (Address_Size c).run v = (.ok (scanAddressSize c), v) :=
    addressSize_scan c hinv.1
  obtain ⟨h1, h3, h4, h5, h6⟩ := hinv
  cases c
  cases h1; cases h3; cases h4; cases h5; cases h6; cases haddr
  have hmode : In64BitMode (afterFetches s (pre.length + 1)) := in64BitMode_of_userCodeSegment hcs hlma
  generalize afterFetches s (pre.length + 1) = v at hmode hmap ⊢
  refine (partialSpecM_bind_run _ _ (partialSpecM_liftTotal_run _ (hasz v))).trans ?_
  refine (partialSpecM_bind_run (liftM (Std.Bits.Add_int (n := 64) s.RIP pre.length)) _
    (value := BitVec.add s.RIP (BitVec.ofNat 64 pre.length)) rfl).trans ?_
  refine (partialSpecM_bind_run _ _ (partialSpecM_liftTotal_run _
    (scanByte_noExtendedPrefix op.toBitVec hop v _))).trans ?_
  simp only [HAnd.hAnd, AndOp.and, strictAnd, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  refine (partialSpecM_bind_run _ _ (partialSpecM_liftTotal_run _
    (operandSize_scan _ ⟨rfl, rfl, rfl, rfl, rfl⟩ v hmode))).trans ?_
  refine (partialSpecM_bind_run (liftM (Std.Bits.Add_int (n := 64) s.RIP pre.length)) _
    (value := BitVec.add s.RIP (BitVec.ofNat 64 pre.length)) rfl).trans ?_
  refine (partialSpecM_bind_run _ _ (partialSpecM_liftTotal_run _ hmap)).trans ?_
  rfl

/-- The scan never sets REX2's B4 bit. -/
theorem scanContext_rex_b4 (seg : Segment) (segs : PrefixSegments) (pre : List UInt8) :
    (scanContext seg segs pre).rex_b4 = 0 := by
  have hfold : ∀ (pre : List UInt8) (ctx : Instruction_Context), ctx.rex_b4 = 0 →
      (pre.foldl (prefixUpdate segs) ctx).rex_b4 = 0 := by
    intro pre
    induction pre with
    | nil => exact fun _ h => h
    | cons p pre ih =>
      intro ctx h
      refine ih _ ?_
      unfold prefixUpdate
      repeat' split
      all_goals exact h
  exact hfold pre (legacyContext seg) rfl

/-- Without an address-size prefix among the scanned prefixes the address size is 64. -/
theorem scanContext_address_size (seg : Segment) (segs : PrefixSegments) (pre : List UInt8)
    (hasz : (scanContext seg segs pre).asz_prefix_present = false) :
    (scanContext seg segs pre).address_size = 64 := by
  have h : (pre.foldl (prefixUpdate segs) (legacyContext seg)).asz_prefix_present = false := hasz
  show scanAddressSize (pre.foldl (prefixUpdate segs) (legacyContext seg)) = 64
  simp [scanAddressSize, h]

/-- The scan's context has no REX2 prefix. -/
theorem scanContext_rex2_prefix_present (seg : Segment) (segs : PrefixSegments)
    (pre : List UInt8) : (scanContext seg segs pre).rex2_prefix_present = false :=
  (ScanInv.foldl (segs := segs) (ctx := legacyContext seg) ⟨rfl, rfl, rfl, rfl, rfl⟩ pre).2.1

/--
The prefix scan for `pre ++ op :: rest` with a one-byte legacy opcode `op`: `pre.length + 1`
fetches, then `Decode_Legacy_0` at the opcode (RIP + `pre.length`) in `scanContext`.
-/
theorem fetchAndExecute_scan_legacy0_of_fetchReady [X86.Machine.Bindings]
    (s : RamState) (hf : FetchReady s) (pre : List UInt8) (op : UInt8) (rest : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hop : LegacyOpcode op.toBitVec) (hlen : pre.length < 15)
    (hcode : BytesAt s s.RIP (pre ++ op :: rest))
    (hlow : s.RIP.toNat + (pre ++ op :: rest).length ≤ 2^32) :
    Fetch_And_Execute.run s =
      (completeDecoded (scanPreservesRepeat op.toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre)) (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 pre.length))
        (scanContext s.DS (PrefixSegments.ofState s) pre))).run (afterFetches s (pre.length + 1)) := by
  have h15 : (op.toBitVec == 15) = false := hop.2 15 (by decide)
  unfold Fetch_And_Execute
  refine (partialSpecM_get_bind_run _ s).trans ?_
  refine (partialSpecM_bind_run _ _ (decodePrefixes_run s _ hf pre op rest hpre hop.scanOpcode hlen
    hcode hlow _ _ (decodeLegacyMap_run_legacy0 _ _ h15 _))).trans ?_
  simp only [scanContext_rex2_prefix_present, HAnd.hAnd, AndOp.and, strictAnd, HOr.hOr, OrOp.or,
    strictOr, Bool.not_false, Bool.and_true, Bool.false_or, beq_self_eq_true]
  unfold completeDecoded scanPreservesRepeat
  cases hrep : ((scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix != 0) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.true_and] <;> rfl

/--
The `0F` escape: the prefix scan for `pre ++ 0F :: op2 :: rest`, with `op2` not `38` or `3A` (the
three-byte maps). `Fetch_And_Execute` fetches the prefixes and `0F` (`pre.length + 1` fetches),
then `op2` (one more), and runs `Decode_Legacy_1` at `op2` (RIP + `pre.length + 1`) in
`scanContext`. `Decode_Legacy_1` fetches `op2` again, so as for one-byte opcodes the fetch count
is the instruction length plus one.
-/
theorem fetchAndExecute_scan_legacy1_of_fetchReady [X86.Machine.Bindings]
    (s : RamState) (hf : FetchReady s) (pre : List UInt8) (op2 : UInt8) (rest : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hop2 : op2 ≠ 0x38 ∧ op2 ≠ 0x3A)
    (hlen : pre.length + 1 < 15) (hcode : BytesAt s s.RIP (pre ++ 0x0F :: op2 :: rest))
    (hlow : s.RIP.toNat + (pre ++ 0x0F :: op2 :: rest).length ≤ 2^32) :
    Fetch_And_Execute.run s =
      (completeDecoded false (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)))
        (scanContext s.DS (PrefixSegments.ofState s) pre))).run (afterFetches s (pre.length + 2)) := by
  have hadd : BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 pre.length)) 1#64 =
      BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)) :=
    (BitVec.add_assoc s.RIP (BitVec.ofNat 64 pre.length) 1#64).trans
      (by rw [BitVec.ofNat_add]; rfl)
  have hf2 := memFetch_run_of_bytesAt s (pre.length + 1) hf hcode hlow (pre.length + 1) (by simp) hlen
  simp only [List.getElem_append_right (Nat.le_add_right _ 1), Nat.add_sub_cancel_left,
    List.getElem_cons_succ, List.getElem_cons_zero] at hf2
  rw [← hadd] at hf2
  have h56 : (op2.toBitVec == 56) = false := by
    simpa [← UInt8.toBitVec_inj] using hop2.1
  have h58 : (op2.toBitVec == 58) = false := by
    simpa [← UInt8.toBitVec_inj] using hop2.2
  unfold Fetch_And_Execute
  refine (partialSpecM_get_bind_run _ s).trans ?_
  refine (partialSpecM_bind_run _ _ (decodePrefixes_run s _ hf pre 0x0F (op2 :: rest) hpre
    scanOpcode_0F (by omega) hcode hlow _ _
    (decodeLegacyMap_run_legacy1 _ _ _ _ hf2 h56 h58))).trans ?_
  rw [hadd]
  simp only [scanContext_rex2_prefix_present, HAnd.hAnd, AndOp.and, strictAnd, HOr.hOr, OrOp.or,
    strictOr, Bool.not_false, Bool.and_true, Bool.false_or,
    show (Instruction_Map.Map_Legacy_1 == Instruction_Map.Map_Legacy_0) = false from rfl,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  rfl

/-! ### Step wrappers -/

/-- `fetchAndExecute_scan_legacy0_of_fetchReady` from the state `Fetch_And_Execute` starts from, under `ReadyToStep`. -/
theorem fetchAndExecute_scan_legacy0 [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8) (op : UInt8) (rest : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hop : LegacyOpcode op.toBitVec) (hlen : pre.length < 15)
    (hcode : BytesAt s s.RIP (pre ++ op :: rest))
    (hlow : s.RIP.toNat + (pre ++ op :: rest).length ≤ 2^32) :
    Fetch_And_Execute.run (beforeFetch s) =
      (completeDecoded (scanPreservesRepeat op.toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre)) (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 pre.length))
        (scanContext s.DS (PrefixSegments.ofState s) pre))).run (afterFetches (beforeFetch s) (pre.length + 1)) :=
  fetchAndExecute_scan_legacy0_of_fetchReady (beforeFetch s) h.fetchReady pre op rest hpre hop hlen hcode hlow

/--
Step wrapper for prefixes `pre` (any the scan covers, `ScanPrefix`) and a one-byte legacy opcode
(see `step_rex_legacy0`): if the legacy decoder, run at the opcode from the state after the
`pre.length + 1` prefix-scan fetches, returns normally with state `t` in 64-bit mode, then
`step s` runs normally and its result is `finishStep` of the decoded-completion state.
-/
theorem step_scan_legacy0 [Bindings]
    (s t : RamState) (h : ReadyToStep s) (pre : List UInt8) (op : UInt8) (rest : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hop : LegacyOpcode op.toBitVec) (hlen : pre.length < 15)
    (hcode : BytesAt s s.RIP (pre ++ op :: rest))
    (hlow : s.RIP.toNat + (pre ++ op :: rest).length ≤ 2^32)
    (hdecode : (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 pre.length))
        (scanContext s.DS (PrefixSegments.ofState s) pre)).run (afterFetches (beforeFetch s) (pre.length + 1)) =
          some (.ok (), t))
    (hmode : In64BitMode t) :
    X86.Machine.step s = some (.next (finishStep (finishDecoded (scanPreservesRepeat op.toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre)) t))) := by
  apply step_of_fetchAndExecute s _ h.readyToStepCore _
    (hmode.of_cs_lma_eq (by cases (scanPreservesRepeat op.toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre)) <;> rfl) (by cases (scanPreservesRepeat op.toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre)) <;> rfl))
  rw [fetchAndExecute_scan_legacy0 s h pre op rest hpre hop hlen hcode hlow]
  exact completeDecoded_run_ok _ _ hdecode

/--
`step_scan_legacy0` under `ReadyMidRep` (the repeat flag may be set): the step wrapper for the
iterations of a `REP` string instruction with any prefix list `pre` the scan covers.
-/
theorem step_scan_legacy0_midRep [Bindings]
    (s t : RamState) (h : ReadyMidRep s) (pre : List UInt8) (op : UInt8) (rest : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hop : LegacyOpcode op.toBitVec) (hlen : pre.length < 15)
    (hcode : BytesAt s s.RIP (pre ++ op :: rest))
    (hlow : s.RIP.toNat + (pre ++ op :: rest).length ≤ 2^32)
    (hdecode : (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 pre.length))
        (scanContext s.DS (PrefixSegments.ofState s) pre)).run (afterFetches (beforeFetch s) (pre.length + 1)) =
          some (.ok (), t))
    (hmode : In64BitMode t) :
    X86.Machine.step s = some (.next (finishStep (finishDecoded (scanPreservesRepeat op.toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre)) t))) := by
  apply step_of_fetchAndExecute s _ h.readyToStepCore _
    (hmode.of_cs_lma_eq (by cases (scanPreservesRepeat op.toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre)) <;> rfl) (by cases (scanPreservesRepeat op.toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre)) <;> rfl))
  rw [fetchAndExecute_scan_legacy0_of_fetchReady (beforeFetch s) h.fetchReady pre op rest hpre hop
    hlen hcode hlow]
  exact completeDecoded_run_ok _ _ hdecode

/-- `fetchAndExecute_scan_legacy1_of_fetchReady` from the state `Fetch_And_Execute` starts from, under `ReadyToStep`. -/
theorem fetchAndExecute_scan_legacy1 [Bindings]
    (s : RamState) (h : ReadyToStep s) (pre : List UInt8) (op2 : UInt8) (rest : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hop2 : op2 ≠ 0x38 ∧ op2 ≠ 0x3A)
    (hlen : pre.length + 1 < 15) (hcode : BytesAt s s.RIP (pre ++ 0x0F :: op2 :: rest))
    (hlow : s.RIP.toNat + (pre ++ 0x0F :: op2 :: rest).length ≤ 2^32) :
    Fetch_And_Execute.run (beforeFetch s) =
      (completeDecoded false (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)))
        (scanContext s.DS (PrefixSegments.ofState s) pre))).run (afterFetches (beforeFetch s) (pre.length + 2)) :=
  fetchAndExecute_scan_legacy1_of_fetchReady (beforeFetch s) h.fetchReady pre op2 rest hpre hop2 hlen hcode hlow

/--
Step wrapper for prefixes `pre`, the `0F` escape and a second opcode byte `op2` (not `38`/`3A`):
if `Decode_Legacy_1`, run at `op2` from the state after the `pre.length + 2` scan fetches, returns
normally with state `t` in 64-bit mode, then `step s` runs normally after clearing stale
REP continuation and applying `finishStep`.
-/
theorem step_scan_legacy1 [Bindings]
    (s t : RamState) (h : ReadyToStep s) (pre : List UInt8) (op2 : UInt8) (rest : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hop2 : op2 ≠ 0x38 ∧ op2 ≠ 0x3A)
    (hlen : pre.length + 1 < 15) (hcode : BytesAt s s.RIP (pre ++ 0x0F :: op2 :: rest))
    (hlow : s.RIP.toNat + (pre ++ 0x0F :: op2 :: rest).length ≤ 2^32)
    (hdecode : (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)))
        (scanContext s.DS (PrefixSegments.ofState s) pre)).run (afterFetches (beforeFetch s) (pre.length + 2)) =
          some (.ok (), t))
    (hmode : In64BitMode t) :
    X86.Machine.step s = some (.next (finishStep (finishDecoded false t))) := by
  apply step_of_fetchAndExecute s _ h.readyToStepCore _
    (hmode.of_cs_lma_eq (by cases false <;> rfl) (by cases false <;> rfl))
  rw [fetchAndExecute_scan_legacy1 s h pre op2 rest hpre hop2 hlen hcode hlow]
  exact completeDecoded_run_ok _ _ hdecode

/-! ### Contexts for concrete prefix shapes

`scanContext` reduces by `rfl` on a concrete prefix list; these name the results for common
shapes, and give the operand size each selects. -/

theorem scanPrefix_66 : ScanPrefix 0x66 := .inr (.inl rfl)
theorem scanPrefix_2e : ScanPrefix 0x2E := .inr (.inr (.inl rfl))
theorem scanPrefix_f3 : ScanPrefix 0xF3 := .inr (.inr (.inr (.inl rfl)))
theorem scanPrefix_64 : ScanPrefix 0x64 := .inr (.inr (.inr (.inr (.inl rfl))))
theorem scanPrefix_65 : ScanPrefix 0x65 := .inr (.inr (.inr (.inr (.inr (.inl rfl)))))
theorem scanPrefix_f0 : ScanPrefix 0xF0 := .inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
theorem scanPrefix_f2 : ScanPrefix 0xF2 :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))))
theorem scanPrefix_67 : ScanPrefix 0x67 :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl)))))))
theorem RexPrefix.scanPrefix {rex : UInt8} (h : RexPrefix rex.toBitVec) : ScanPrefix rex := .inl h

/-- Any list of `66` and `2E` bytes is a list of scan prefixes. -/
theorem scanPrefix_of_66_2e {pre : List UInt8} (h : ∀ p ∈ pre, p = 0x66 ∨ p = 0x2E) :
    ∀ p ∈ pre, ScanPrefix p := fun p hp => (h p hp).elim
  (fun h => h ▸ scanPrefix_66) (fun h => h ▸ scanPrefix_2e)

/-- The decode context after a `66` prefix (no REX): operand size 16. -/
noncomputable def oszContext (segment : Segment) : Instruction_Context :=
  {legacyContext segment with osz_prefix_present := true, operand_size := 16}

/-- After `66` (and no REX.W) the operand size is 16. -/
theorem oszContext_operand_size (segment : Segment) : (oszContext segment).operand_size = 16 := rfl

/-- The decode context after `66` and a REX prefix `rex`: operand size 64 if REX.W, else 16. -/
noncomputable def oszRexContext (segment : Segment) (rex : BitVec 8) : Instruction_Context :=
  {rexContext segment rex with
    osz_prefix_present := true
    operand_size := if rex.getLsbD 3 then 64 else 16}

/-- After `66` and REX.W the operand size is 64 (REX.W wins). -/
theorem RexWPrefix.operand_size_osz {rex : BitVec 8} (h : RexWPrefix rex) (segment : Segment) :
    (oszRexContext segment rex).operand_size = 64 := by
  simp only [RexWPrefix, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- After `66` and a REX prefix with W = 0 the operand size is 16. -/
theorem RexNoWPrefix.operand_size_osz {rex : BitVec 8} (h : RexNoWPrefix rex) (segment : Segment) :
    (oszRexContext segment rex).operand_size = 16 := by
  simp only [RexNoWPrefix, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- No prefix: the default context (operand size 32). -/
theorem scanContext_nil (seg : Segment) (segs : PrefixSegments) : scanContext seg segs [] = legacyContext seg := rfl

/-- A REX prefix alone: `rexContext` (operand size 64 with REX.W, else 32). -/
theorem scanContext_rex (seg : Segment) (segs : PrefixSegments) {rex : UInt8} (h : RexPrefix rex.toBitVec) :
    scanContext seg segs [rex] = rexContext seg rex.toBitVec := by
  simp only [RexPrefix, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    (obtain rfl : rex = _ := UInt8.toBitVec_inj.mp h; rfl)

/-- `F3` alone: `repContext`. -/
theorem scanContext_f3 (seg : Segment) (segs : PrefixSegments) : scanContext seg segs [0xF3] = repContext seg := rfl

/-- `F3` then REX: `repRexContext`. -/
theorem scanContext_f3_rex (seg : Segment) (segs : PrefixSegments) {rex : UInt8} (h : RexPrefix rex.toBitVec) :
    scanContext seg segs [0xF3, rex] = repRexContext seg rex.toBitVec := by
  simp only [RexPrefix, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    (obtain rfl : rex = _ := UInt8.toBitVec_inj.mp h; rfl)

/-- `F2` alone: `repneContext`. -/
theorem scanContext_f2 (seg : Segment) (segs : PrefixSegments) :
    scanContext seg segs [0xF2] = repneContext seg := rfl

/-- `F2` then REX: `repneRexContext`. -/
theorem scanContext_f2_rex (seg : Segment) (segs : PrefixSegments) {rex : UInt8}
    (h : RexPrefix rex.toBitVec) :
    scanContext seg segs [0xF2, rex] = repneRexContext seg rex.toBitVec := by
  simp only [RexPrefix, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    (obtain rfl : rex = _ := UInt8.toBitVec_inj.mp h; rfl)

/-- `66` alone: `oszContext` (operand size 16). -/
theorem scanContext_66 (seg : Segment) (segs : PrefixSegments) : scanContext seg segs [0x66] = oszContext seg := rfl

/-- After `66` and a REX prefix with W = 0, REX.W is clear. -/
theorem RexNoWPrefix.rex_w_osz {rex : BitVec 8} (h : RexNoWPrefix rex) (segment : Segment) :
    (oszRexContext segment rex).rex_w = 0 := by
  simp only [RexNoWPrefix, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `66` then REX: `oszRexContext`. -/
theorem scanContext_66_rex (seg : Segment) (segs : PrefixSegments) {rex : UInt8} (h : RexPrefix rex.toBitVec) :
    scanContext seg segs [0x66, rex] = oszRexContext seg rex.toBitVec := by
  simp only [RexPrefix, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    (obtain rfl : rex = _ := UInt8.toBitVec_inj.mp h; rfl)

/-- `66 2E` (the `66 2E 0F 1F …` NOP): `oszContext`, as `66` alone (`2E` does nothing in
64-bit mode). -/
theorem scanContext_66_2e (seg : Segment) (segs : PrefixSegments) :
    scanContext seg segs [0x66, 0x2E] = oszContext seg := rfl

/-- `66 66 66 2E` (the `66 66 66 2E 0F 1F …` NOP): the same as `66 2E`. -/
theorem scanContext_66x3_2e (seg : Segment) (segs : PrefixSegments) :
    scanContext seg segs [0x66, 0x66, 0x66, 0x2E] = oszContext seg := rfl

/-- `66 66 66 66 2E` (the `66 66 66 66 2E 0F 1F …` NOP): the same as `66 2E`. -/
theorem scanContext_66x4_2e (seg : Segment) (segs : PrefixSegments) :
    scanContext seg segs [0x66, 0x66, 0x66, 0x66, 0x2E] = oszContext seg := rfl

/-! ### Segment overrides

In 64-bit mode only FS (`64`) and GS (`65`) override a memory operand's segment. -/

/-- A segment register a segment-override prefix selects in 64-bit mode. -/
inductive SegReg where
  | fs
  | gs
  deriving DecidableEq

/-- The prefix byte selecting the segment register: `64` (FS) or `65` (GS). -/
def SegReg.prefixByte : SegReg → UInt8
  | .fs => 0x64
  | .gs => 0x65

/-- The segment the register's prefix puts in the decode context. -/
def SegReg.select (r : SegReg) (segs : PrefixSegments) : Segment :=
  match r with
  | .fs => segs.fs
  | .gs => segs.gs

/-- The segment register of `s`. -/
abbrev SegReg.read {σ : Type} (r : SegReg) (s : X86.State σ) : Segment := r.select (PrefixSegments.ofState s)

theorem SegReg.scanPrefix (r : SegReg) : ScanPrefix r.prefixByte := by
  cases r
  · exact scanPrefix_64
  · exact scanPrefix_65

/-- The decode context after a segment-override prefix for segment `sr` (no REX). -/
noncomputable def segContext (seg sr : Segment) : Instruction_Context :=
  {legacyContext seg with segment := sr, seg_prefix_present := true}

/-- The decode context after a segment-override prefix for segment `sr` and a REX prefix `rex`. -/
noncomputable def segRexContext (seg sr : Segment) (rex : BitVec 8) : Instruction_Context :=
  {rexContext seg rex with segment := sr, seg_prefix_present := true}

/-- `64` or `65` alone: `segContext` with FS or GS. -/
theorem scanContext_seg (seg : Segment) (segs : PrefixSegments) (r : SegReg) :
    scanContext seg segs [r.prefixByte] = segContext seg (r.select segs) := by
  cases r <;> rfl

/-- `64` or `65` then REX: `segRexContext` with FS or GS. -/
theorem scanContext_seg_rex (seg : Segment) (segs : PrefixSegments) (r : SegReg) {rex : UInt8}
    (h : RexPrefix rex.toBitVec) :
    scanContext seg segs [r.prefixByte, rex] = segRexContext seg (r.select segs) rex.toBitVec := by
  simp only [RexPrefix, List.mem_cons, List.not_mem_nil, or_false] at h
  cases r <;>
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    (obtain rfl : rex = _ := UInt8.toBitVec_inj.mp h; rfl)

/-- After a segment prefix and REX.W the operand size is 64. -/
theorem RexWPrefix.operand_size_seg {rex : BitVec 8} (h : RexWPrefix rex) (seg sr : Segment) :
    (segRexContext seg sr rex).operand_size = 64 :=
  h.operand_size seg

/-- After a segment prefix and a REX prefix with W = 0 the operand size is 32. -/
theorem RexNoWPrefix.operand_size_seg {rex : BitVec 8} (h : RexNoWPrefix rex) (seg sr : Segment) :
    (segRexContext seg sr rex).operand_size = 32 :=
  h.operand_size seg

/-- The decode context `ctx` with an FS/GS prefix for segment `sr` in front of its prefixes: the
segment is `sr`, a segment override, and `no_track_prefix` is cleared (`scanContext_seg_cons`). -/
noncomputable def withSeg (ctx : Instruction_Context) (sr : Segment) : Instruction_Context :=
  {ctx with no_track_prefix := false, segment := sr, seg_prefix_present := true}

/-- A prefix byte that is not a segment prefix (`2E`, `64`, `65`). -/
abbrev NoSegPrefix (p : UInt8) : Prop :=
  p ≠ 0x2E ∧ p ≠ 0x64 ∧ p ≠ 0x65

theorem noSegPrefix_66 : NoSegPrefix 0x66 := by decide
theorem noSegPrefix_f3 : NoSegPrefix 0xF3 := by decide
theorem noSegPrefix_f0 : NoSegPrefix 0xF0 := by decide
theorem noSegPrefix_f2 : NoSegPrefix 0xF2 := by decide
theorem noSegPrefix_67 : NoSegPrefix 0x67 := by decide

theorem RexPrefix.noSegPrefix {rex : UInt8} (h : RexPrefix rex.toBitVec) : NoSegPrefix rex := by
  simp only [RexPrefix, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    (obtain rfl : rex = _ := UInt8.toBitVec_inj.mp h; decide)

theorem noSegPrefix_nil : ∀ q ∈ ([] : List UInt8), NoSegPrefix q := by simp

theorem noSegPrefix_cons {p : UInt8} {pre : List UInt8} (hp : NoSegPrefix p)
    (h : ∀ q ∈ pre, NoSegPrefix q) : ∀ q ∈ p :: pre, NoSegPrefix q := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hp
  · exact h q hq

/-- A prefix other than a segment prefix commutes with `withSeg`. -/
theorem prefixUpdate_withSeg (segs : PrefixSegments) (ctx : Instruction_Context) (sr : Segment)
    {p : UInt8} (hp : NoSegPrefix p) :
    prefixUpdate segs (withSeg ctx sr) p = withSeg (prefixUpdate segs ctx p) sr := by
  obtain ⟨h1, h2, h3⟩ := hp
  unfold prefixUpdate
  by_cases h66 : p = 0x66
  · simp only [h66, ↓reduceIte]; rfl
  by_cases hf3 : p = 0xF3
  · simp only [hf3, ↓reduceIte]; rfl
  by_cases hf0 : p = 0xF0
  · simp only [hf0, ↓reduceIte]; rfl
  by_cases hf2 : p = 0xF2
  · simp only [hf2, ↓reduceIte]; rfl
  by_cases h67 : p = 0x67
  · simp only [h67, ↓reduceIte]; rfl
  simp only [h66, h1, hf3, h2, h3, hf0, hf2, h67, ↓reduceIte]
  rfl

/-- An FS/GS prefix (`64`, `65`) followed by prefixes that are not segment prefixes: the context
of those prefixes with the segment override (`withSeg`). -/
theorem scanContext_seg_cons (seg : Segment) (segs : PrefixSegments) (r : SegReg)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, NoSegPrefix p) :
    scanContext seg segs (r.prefixByte :: pre) =
      withSeg (scanContext seg segs pre) (r.select segs) := by
  have hfold : ∀ (ctx : Instruction_Context) (pre : List UInt8), (∀ p ∈ pre, NoSegPrefix p) →
      pre.foldl (prefixUpdate segs) (withSeg ctx (r.select segs)) =
        withSeg (pre.foldl (prefixUpdate segs) ctx) (r.select segs) := by
    intro ctx pre hpre
    induction pre generalizing ctx with
    | nil => rfl
    | cons p pre ih =>
      simp only [List.foldl_cons]
      rw [prefixUpdate_withSeg _ _ _ (hpre p (by simp)),
        ih _ (fun q hq => hpre q (by simp [hq]))]
  have h0 : prefixUpdate segs (legacyContext seg) r.prefixByte =
      withSeg (legacyContext seg) (r.select segs) := by
    cases r <;> rfl
  unfold scanContext
  simp only [List.foldl_cons, h0, hfold _ _ hpre]
  rfl

/-! ### The LOCK prefix

`F0` only sets `lock_prefix_present` (and clears the REX bits, like every legacy prefix), so it
commutes with every other prefix: in front of any prefix list it gives their context with the lock
flag set. -/

/-- The decode context `ctx` with a LOCK prefix (`F0`) in front of its prefixes
(`scanContext_lock_cons`). -/
def withLock (ctx : Instruction_Context) : Instruction_Context :=
  {ctx with lock_prefix_present := true}

theorem withLock_lock_prefix_present (ctx : Instruction_Context) :
    (withLock ctx).lock_prefix_present = true := rfl

/-- Every prefix the scan covers commutes with `withLock`. -/
theorem prefixUpdate_withLock (segs : PrefixSegments) (ctx : Instruction_Context) (p : UInt8) :
    prefixUpdate segs (withLock ctx) p = withLock (prefixUpdate segs ctx p) := by
  unfold prefixUpdate
  repeat' split
  all_goals rfl

/-- A LOCK prefix (`F0`) followed by any prefixes: the context of those prefixes with the lock
flag set (`withLock`). -/
theorem scanContext_lock_cons (seg : Segment) (segs : PrefixSegments) (pre : List UInt8) :
    scanContext seg segs (0xF0 :: pre) = withLock (scanContext seg segs pre) := by
  have hfold : ∀ (ctx : Instruction_Context) (pre : List UInt8),
      pre.foldl (prefixUpdate segs) (withLock ctx) =
        withLock (pre.foldl (prefixUpdate segs) ctx) := by
    intro ctx pre
    induction pre generalizing ctx with
    | nil => rfl
    | cons p pre ih => simp only [List.foldl_cons, prefixUpdate_withLock, ih]
  have h0 : prefixUpdate segs (legacyContext seg) 0xF0 = withLock (legacyContext seg) := rfl
  unfold scanContext
  simp only [List.foldl_cons, h0, hfold]
  rfl

/-- The scan covers a LOCK prefix in front of prefixes it covers. -/
theorem scanPrefix_lock_cons {pre : List UInt8} (h : ∀ p ∈ pre, ScanPrefix p) :
    ∀ p ∈ 0xF0 :: pre, ScanPrefix p := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact scanPrefix_f0
  · exact h p hp

/-- The scan covers an FS/GS prefix in front of prefixes it covers. -/
theorem scanPrefix_seg_cons (r : SegReg) {pre : List UInt8} (h : ∀ p ∈ pre, ScanPrefix p) :
    ∀ p ∈ r.prefixByte :: pre, ScanPrefix p := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact r.scanPrefix
  · exact h p hp

/-! ### The address-size prefix

`67` only sets `asz_prefix_present` (and clears the REX bits, like every legacy prefix), so it
commutes with every other prefix: in front of any prefix list it gives their context at address
size 32 (`scanAddressSize`). -/

/-- The decode context `ctx` with an address-size prefix (`67`) in front of its prefixes
(`scanContext_asz_cons`): `asz_prefix_present` set, address size 32. -/
def withAsz (ctx : Instruction_Context) : Instruction_Context :=
  {ctx with asz_prefix_present := true, address_size := 32}

theorem withAsz_address_size (ctx : Instruction_Context) : (withAsz ctx).address_size = 32 := rfl

/-- Every prefix the scan covers commutes with setting `asz_prefix_present`. -/
theorem prefixUpdate_asz (segs : PrefixSegments) (ctx : Instruction_Context) (p : UInt8) :
    prefixUpdate segs {ctx with asz_prefix_present := true} p =
      {prefixUpdate segs ctx p with asz_prefix_present := true} := by
  prefix_cases p => rfl

/-- An address-size prefix (`67`) followed by any prefixes: the context of those prefixes at
address size 32 (`withAsz`). -/
theorem scanContext_asz_cons (seg : Segment) (segs : PrefixSegments) (pre : List UInt8) :
    scanContext seg segs (0x67 :: pre) = withAsz (scanContext seg segs pre) := by
  have hfold : ∀ (ctx : Instruction_Context) (pre : List UInt8),
      pre.foldl (prefixUpdate segs) {ctx with asz_prefix_present := true} =
        {pre.foldl (prefixUpdate segs) ctx with asz_prefix_present := true} := by
    intro ctx pre
    induction pre generalizing ctx with
    | nil => rfl
    | cons p pre ih => simp only [List.foldl_cons, prefixUpdate_asz, ih]
  have h0 : prefixUpdate segs (legacyContext seg) 0x67 =
      {legacyContext seg with asz_prefix_present := true} := rfl
  unfold scanContext
  simp only [List.foldl_cons, h0, hfold]
  rfl

/-- The scan covers an address-size prefix in front of prefixes it covers. -/
theorem scanPrefix_asz_cons {pre : List UInt8} (h : ∀ p ∈ pre, ScanPrefix p) :
    ∀ p ∈ 0x67 :: pre, ScanPrefix p := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact scanPrefix_67
  · exact h p hp

/-- An address-size prefix in front of prefixes that are not segment prefixes is not one either. -/
theorem noSegPrefix_asz_cons {pre : List UInt8} (h : ∀ q ∈ pre, NoSegPrefix q) :
    ∀ q ∈ 0x67 :: pre, NoSegPrefix q :=
  noSegPrefix_cons noSegPrefix_67 h

/-! ### Step wrappers for single shapes -/

/-- Step wrapper for `66 op` (an operand-size prefix and a one-byte legacy opcode, e.g. `66 90`,
`66 C7`): two scan fetches, then the legacy decoder at RIP + 1 in `oszContext`. -/
theorem step_66_legacy0 [Bindings]
    (s t : RamState) (h : ReadyToStep s) (op : UInt8) (rest : List UInt8)
    (hop : LegacyOpcode op.toBitVec) (hcode : BytesAt s s.RIP (0x66 :: op :: rest))
    (hlow : s.RIP.toNat + (0x66 :: op :: rest).length ≤ 2^32)
    (hdecode : (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (oszContext s.DS)).run
        (afterFetches (beforeFetch s) 2) = some (.ok (), t))
    (hmode : In64BitMode t) :
    X86.Machine.step s = some (.next (finishStep (finishDecoded false t))) :=
  step_scan_legacy0 s t h [0x66] op rest (by simp [scanPrefix_66]) hop (by decide) hcode hlow
    hdecode hmode

/-- Step wrapper for `66 rex op` (an operand-size prefix, a REX prefix and a one-byte legacy
opcode, e.g. `66 41 01 C0`, `add r8w, ax`): three scan fetches, then the legacy decoder at RIP + 2
in `oszRexContext`. -/
theorem step_66_rex_legacy0 [Bindings]
    (s t : RamState) (h : ReadyToStep s) (rex op : UInt8) (rest : List UInt8)
    (hrex : RexPrefix rex.toBitVec) (hop : LegacyOpcode op.toBitVec)
    (hcode : BytesAt s s.RIP (0x66 :: rex :: op :: rest))
    (hlow : s.RIP.toNat + (0x66 :: rex :: op :: rest).length ≤ 2^32)
    (hdecode : (Decode_Legacy_0 (BitVec.add s.RIP 2#64) (oszRexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 3) = some (.ok (), t))
    (hmode : In64BitMode t) :
    X86.Machine.step s = some (.next (finishStep (finishDecoded false t))) := by
  have hs := step_scan_legacy0 s t h [0x66, rex] op rest
    (by simpa [scanPrefix_66] using hrex.scanPrefix) hop (by simp) hcode hlow
  rw [scanContext_66_rex _ _ hrex] at hs
  exact hs hdecode hmode

/-- Step wrapper for `0F op2` (the two-byte opcode map, no prefix): two scan fetches (`0F`,
`op2`), then `Decode_Legacy_1` at `op2` (RIP + 1) in the default context. -/
theorem step_none_legacy1 [Bindings]
    (s t : RamState) (h : ReadyToStep s) (op2 : UInt8) (rest : List UInt8)
    (hop2 : op2 ≠ 0x38 ∧ op2 ≠ 0x3A) (hcode : BytesAt s s.RIP (0x0F :: op2 :: rest))
    (hlow : s.RIP.toNat + (0x0F :: op2 :: rest).length ≤ 2^32)
    (hdecode : (Decode_Legacy_1 (BitVec.add s.RIP 1#64) (legacyContext s.DS)).run
        (afterFetches (beforeFetch s) 2) = some (.ok (), t))
    (hmode : In64BitMode t) :
    X86.Machine.step s = some (.next (finishStep (finishDecoded false t))) :=
  step_scan_legacy1 s t h [] op2 rest (by simp) hop2 (by decide) hcode hlow hdecode hmode

/-- Step wrapper for `rex 0F op2` (e.g. `41 0F 10`, `movups`): three scan fetches, then
`Decode_Legacy_1` at `op2` (RIP + 2) in `rexContext`. -/
theorem step_rex_legacy1 [Bindings]
    (s t : RamState) (h : ReadyToStep s) (rex op2 : UInt8) (rest : List UInt8)
    (hrex : RexPrefix rex.toBitVec) (hop2 : op2 ≠ 0x38 ∧ op2 ≠ 0x3A)
    (hcode : BytesAt s s.RIP (rex :: 0x0F :: op2 :: rest))
    (hlow : s.RIP.toNat + (rex :: 0x0F :: op2 :: rest).length ≤ 2^32)
    (hdecode : (Decode_Legacy_1 (BitVec.add s.RIP 2#64) (rexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 3) = some (.ok (), t))
    (hmode : In64BitMode t) :
    X86.Machine.step s = some (.next (finishStep (finishDecoded false t))) := by
  refine step_scan_legacy1 s t h [rex] op2 rest (by simpa using hrex.scanPrefix) hop2 (by simp)
    hcode hlow ?_ hmode
  rw [scanContext_rex _ _ hrex]
  exact hdecode

end X86Proofs
