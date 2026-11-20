import X86Proofs.Step.Fetch
import X86Proofs.Step.Wrapper

/-!
# Prefix bytes: decode contexts

The decode contexts `Fetch_And_Execute`'s prefix scan hands to the legacy decoder for the prefix
shapes with names here (`legacyContext`, `rexContext`, `repContext`, `repRexContext`,
`repneContext`, `repneRexContext`), the REX prefix predicates, `LegacyOpcode` (a byte the scan
treats as a one-byte opcode), `currentMode_run` and `addressSize_mode64_run`. The scan itself is
`Step/PrefixScan.lean`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- The decode context `Fetch_And_Execute` builds in 64-bit mode when there is no prefix. -/
noncomputable def legacyContext (segment : X86.Helpers.Segment) : Instruction_Context :=
  {(default : Instruction_Context) with segment := segment, mode := .IA32e_Mode, is_mode64 := true, operand_size := 32, address_size := 64}

theorem currentMode_run (s : RamState) (hcr0 : Prelude.SupportedIntegerCR0 s.CR0)
    (hlma : s.IA32_EFER.LMA = 1) :
    Current_Mode.run s = (.ok .IA32e_Mode, s) := by
  simp [Current_Mode, cr0PE_eq, get, getThe, liftM, bind, ExceptT.bind, ExceptT.run, ExceptT.mk,
    StateT.bind, ExceptT.bindCont, MonadStateOf.get, monadLift, MonadLift.monadLift, pure,
    ExceptT.pure, StateT.pure, StateT.get, ExceptT.lift, Functor.map, StateT.map, Bind.bind,
    x86_runtime, (supportedIntegerCR0_extractLsb_pe hcr0), hlma]

/-- lean-x86's `Address_Size` in 64-bit mode: 32 with an address-size prefix (`67`), else 64;
the state is unchanged. -/
theorem addressSize_mode64_run (ctx : Instruction_Context) (hm64 : ctx.is_mode64 = true)
    (s : RamState) :
    (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run s =
      (.ok (if ctx.asz_prefix_present then 32 else 64), s) := by
  cases hasz : ctx.asz_prefix_present <;> simp [Address_Size, hm64, hasz]

/--
A byte the prefix scan treats as a one-byte legacy opcode: not REX, not a legacy prefix, not a
VEX/EVEX/REX2 escape and not `0F`.
-/
noncomputable def LegacyOpcode (byte : BitVec 8) : Prop :=
  (BitVec.and byte 240#8 == 64#8) = false ∧
  ∀ n : BitVec 8, n ∈ [38,46,54,62,100,101,102,103,240,242,243,98,196,197,213,15] → (byte == n) = false

theorem legacyOpcode_of_check (byte : BitVec 8)
    (h : (BitVec.and byte 240#8 == 64#8) = false ∧
      byte ∉ ([38,46,54,62,100,101,102,103,240,242,243,98,196,197,213,15] : List (BitVec 8))) :
    LegacyOpcode byte := by
  refine ⟨h.1, ?_⟩
  intro n hn
  apply beq_eq_false_iff_ne.mpr
  intro he
  subst n
  exact h.2 hn

/-- REX.R (bit 2): the top bit of the ModRM `reg` register number. -/
def rexR (rex : BitVec 8) : BitVec 1 := rex.extractLsb' 2 1

/-- REX.B (bit 0): the top bit of the ModRM `rm` register number. -/
def rexB (rex : BitVec 8) : BitVec 1 := rex.extractLsb' 0 1

/-- REX.X (bit 1): the top bit of the SIB index register number. -/
def rexX (rex : BitVec 8) : BitVec 1 := rex.extractLsb' 1 1

/-- The decode context after a REX prefix `rex`: REX.W/R/X/B bits recorded, operand size 64 if W. -/
noncomputable def rexContext (segment : X86.Helpers.Segment) (rex : BitVec 8) : Instruction_Context :=
  {legacyContext segment with
    rex_prefix_present := true,
    rex_w := rex.extractLsb' 3 1, rex_r3 := rexR rex,
    rex_x3 := rex.extractLsb' 1 1, rex_b3 := rexB rex,
    operand_size := if rex.getLsbD 3 then 64 else 32}

/-- `rex` is a REX prefix byte (`40`–`4F`). -/
noncomputable def RexPrefix (rex : BitVec 8) : Prop :=
  rex ∈ [0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47,0x48,0x49,0x4a,0x4b,0x4c,0x4d,0x4e,0x4f]

/-- `rex` is a REX prefix byte with W = 1 (`48`–`4F`): 64-bit operand size. -/
def RexWPrefix (rex : BitVec 8) : Prop :=
  rex ∈ [0x48,0x49,0x4a,0x4b,0x4c,0x4d,0x4e,0x4f]

theorem RexWPrefix.rexPrefix {rex : BitVec 8} (h : RexWPrefix rex) : RexPrefix rex := by
  simp only [RexWPrefix, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [RexPrefix]

/-- After a REX.W prefix the operand size is 64. -/
theorem RexWPrefix.operand_size {rex : BitVec 8} (h : RexWPrefix rex) (segment : X86.Helpers.Segment) :
    (rexContext segment rex).operand_size = 64 := by
  simp only [RexWPrefix, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- After a REX.W prefix, REX.W is recorded in the context. -/
theorem RexWPrefix.rex_w {rex : BitVec 8} (h : RexWPrefix rex) (segment : X86.Helpers.Segment) :
    (rexContext segment rex).rex_w = 1 := by
  simp only [RexWPrefix, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `rex` is a REX prefix byte with W = 0 (`40`–`47`): operand size 32 (no `66` prefix), REX.R and
REX.B still extend the register numbers. -/
def RexNoWPrefix (rex : BitVec 8) : Prop :=
  rex ∈ [0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47]

theorem RexNoWPrefix.rexPrefix {rex : BitVec 8} (h : RexNoWPrefix rex) : RexPrefix rex := by
  simp only [RexNoWPrefix, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [RexPrefix]

/-- After a REX prefix with W = 0 the operand size is 32. -/
theorem RexNoWPrefix.operand_size {rex : BitVec 8} (h : RexNoWPrefix rex) (segment : X86.Helpers.Segment) :
    (rexContext segment rex).operand_size = 32 := by
  simp only [RexNoWPrefix, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- After a REX prefix with W = 0, REX.W is clear in the context. -/
theorem RexNoWPrefix.rex_w {rex : BitVec 8} (h : RexNoWPrefix rex) (segment : X86.Helpers.Segment) :
    (rexContext segment rex).rex_w = 0 := by
  simp only [RexNoWPrefix, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Without a prefix the operand size is 32. -/
theorem legacyContext_operand_size (segment : X86.Helpers.Segment) :
    (legacyContext segment).operand_size = 32 := rfl

/-- The decode context after an `F3` (REP) prefix. -/
noncomputable def repContext (segment : X86.Helpers.Segment) : Instruction_Context :=
  {legacyContext segment with rep_prefix := 243}

/-- The decode context after an `F3` (REP) prefix and a REX prefix `rex`. -/
noncomputable def repRexContext (segment : X86.Helpers.Segment) (rex : BitVec 8) :
    Instruction_Context :=
  {rexContext segment rex with rep_prefix := 243}

/-- The decode context after an `F2` (REPNE) prefix. -/
noncomputable def repneContext (segment : X86.Helpers.Segment) : Instruction_Context :=
  {legacyContext segment with rep_prefix := 242}

/-- The decode context after an `F2` (REPNE) prefix and a REX prefix `rex`. -/
noncomputable def repneRexContext (segment : X86.Helpers.Segment) (rex : BitVec 8) :
    Instruction_Context :=
  {rexContext segment rex with rep_prefix := 242}

end X86Proofs
