import X86Proofs.Program.ReadWrite.String
import X86Proofs.Instructions.Cmp.Operation
import X86Proofs.Instructions.Branch.Cond

/-!
# One string compare

`cmpsSpec n t`: what one `CMPS` of `n` bits does with the direction flag clear: compare the
`n`-bit memory operand at RSI with the one at RDI as `CMP` does (the flags of the subtraction,
`cmpSpec`), and advance RSI and RDI by `n / 8`. The bookkeeping of the two data reads (oracle
bits and the `load` trace events) is `dataAccess`. `repeCmpsSpec` and `repneCmpsSpec`: one
iteration of `REPE CMPS` (going on while the operands are equal) and `REPNE CMPS` (while they
differ). `cmpsSegSpec base n t`, `repeCmpsSegSpec`, `repneCmpsSegSpec`: the same with an FS/GS
segment override, the first operand read at `base + RSI`.

lean-x86 lets a binding choose which operand is read first (`Select_Compare_Memory_Order`); when
both reads succeed the order does not matter. The binding must answer: Prelude's contract
`Prelude.Bindings.CompareMemory.SatisfiesSelectors` says it does.
`cmpsDownSpec n t`, `cmpsDownSegSpec base n t`: the same with the direction flag set (DF = 1), the
addresses stepping down by `n / 8` (`compare_string_once_down`, `_down_seg`).
-/

namespace X86Proofs

open X86 X86.Machine

/--
One string compare of `n` bits with DF = 0, from state `t`: the status flags are those of `cmp`
of the `n`-bit value at RSI with the one at RDI, then RSI and RDI advance by `n / 8`.
-/
def cmpsSpec (n : Nat) (t : RamState) : RamState :=
  let u := setFlags (dataAccess (dataAccess t "load") "load")
    (cmpSpec ((Operand.mem (rsi.read t) : Operand n).read t)
      ((Operand.mem (rdi.read t) : Operand n).read t))
  rdi.write (rsi.write u (rsi.read t + BitVec.ofNat 64 (n / 8)))
    (rdi.read t + BitVec.ofNat 64 (n / 8))

/--
`cmpsSpec` with an FS/GS segment override whose base is `base`: the first operand is read at
`base + RSI` (the second, ES:RDI, takes no override).
-/
def cmpsSegSpec (base : BitVec 64) (n : Nat) (t : RamState) : RamState :=
  let u := setFlags (dataAccess (dataAccess t "load") "load")
    (cmpSpec ((Operand.mem (base + rsi.read t) : Operand n).read t)
      ((Operand.mem (rdi.read t) : Operand n).read t))
  rdi.write (rsi.write u (rsi.read t + BitVec.ofNat 64 (n / 8)))
    (rdi.read t + BitVec.ofNat 64 (n / 8))

/--
One string compare of `n` bits with DF = 1, from state `t`: the status flags are those of `cmp`
of the `n`-bit value at RSI with the one at RDI, then RSI and RDI go back by `n / 8`.
-/
def cmpsDownSpec (n : Nat) (t : RamState) : RamState :=
  let u := setFlags (dataAccess (dataAccess t "load") "load")
    (cmpSpec ((Operand.mem (rsi.read t) : Operand n).read t)
      ((Operand.mem (rdi.read t) : Operand n).read t))
  rdi.write (rsi.write u (rsi.read t - BitVec.ofNat 64 (n / 8)))
    (rdi.read t - BitVec.ofNat 64 (n / 8))

/--
`cmpsDownSpec` with an FS/GS segment override whose base is `base`: the first operand is read at
`base + RSI` (the second, ES:RDI, takes no override).
-/
def cmpsDownSegSpec (base : BitVec 64) (n : Nat) (t : RamState) : RamState :=
  let u := setFlags (dataAccess (dataAccess t "load") "load")
    (cmpSpec ((Operand.mem (base + rsi.read t) : Operand n).read t)
      ((Operand.mem (rdi.read t) : Operand n).read t))
  rdi.write (rsi.write u (rsi.read t - BitVec.ofNat 64 (n / 8)))
    (rdi.read t - BitVec.ofNat 64 (n / 8))

/-- Whether `REPE CMPS` of `n` bits goes on after the compare at `t`: RCX - 1 is not zero and the
operands at RSI and RDI are equal (ZF). -/
def repeCmpsCont (n : Nat) (t : RamState) : Bool :=
  !(rcx.read t - 1 == 0#64) &&
    (cmpSpec ((Operand.mem (rsi.read t) : Operand n).read t)
      ((Operand.mem (rdi.read t) : Operand n).read t)).ZF

/--
One iteration of `REPE CMPS` of `n` bits with DF = 0 and RCX ≠ 0, from state `t`: one string
compare (`cmpsSpec`) and RCX decremented; if the instruction goes on (`repeCmpsCont`), the repeat
flag is set and the flags are put back as they were.
-/
def repeCmpsSpec (n : Nat) (t : RamState) : RamState :=
  if repeCmpsCont n t then
    { rcx.write (cmpsSpec n t) (rcx.read t - 1) with
      Repeat_String_Operation := true, RFLAGS := t.RFLAGS }
  else { rcx.write (cmpsSpec n t) (rcx.read t - 1) with Repeat_String_Operation := false }

/-- `repeCmpsCont` with an FS/GS segment override whose base is `base`: the first operand at
`base + RSI`. -/
def repeCmpsSegCont (base : BitVec 64) (n : Nat) (t : RamState) : Bool :=
  !(rcx.read t - 1 == 0#64) &&
    (cmpSpec ((Operand.mem (base + rsi.read t) : Operand n).read t)
      ((Operand.mem (rdi.read t) : Operand n).read t)).ZF

/-- `repeCmpsSpec` with an FS/GS segment override whose base is `base` (`cmpsSegSpec`,
`repeCmpsSegCont`). -/
def repeCmpsSegSpec (base : BitVec 64) (n : Nat) (t : RamState) : RamState :=
  if repeCmpsSegCont base n t then
    { rcx.write (cmpsSegSpec base n t) (rcx.read t - 1) with
      Repeat_String_Operation := true, RFLAGS := t.RFLAGS }
  else { rcx.write (cmpsSegSpec base n t) (rcx.read t - 1) with Repeat_String_Operation := false }

/-- Whether `REPNE CMPS` of `n` bits goes on after the compare at `t`: RCX - 1 is not zero and the
operands at RSI and RDI differ (ZF clear). -/
def repneCmpsCont (n : Nat) (t : RamState) : Bool :=
  !(rcx.read t - 1 == 0#64) &&
    !(cmpSpec ((Operand.mem (rsi.read t) : Operand n).read t)
      ((Operand.mem (rdi.read t) : Operand n).read t)).ZF

/--
One iteration of `REPNE CMPS` of `n` bits with DF = 0 and RCX ≠ 0, from state `t`: one string
compare (`cmpsSpec`) and RCX decremented; if the instruction goes on (`repneCmpsCont`), the repeat
flag is set and the flags are put back as they were.
-/
def repneCmpsSpec (n : Nat) (t : RamState) : RamState :=
  if repneCmpsCont n t then
    { rcx.write (cmpsSpec n t) (rcx.read t - 1) with
      Repeat_String_Operation := true, RFLAGS := t.RFLAGS }
  else { rcx.write (cmpsSpec n t) (rcx.read t - 1) with Repeat_String_Operation := false }

/-- `repneCmpsCont` with an FS/GS segment override whose base is `base`: the first operand at
`base + RSI`. -/
def repneCmpsSegCont (base : BitVec 64) (n : Nat) (t : RamState) : Bool :=
  !(rcx.read t - 1 == 0#64) &&
    !(cmpSpec ((Operand.mem (base + rsi.read t) : Operand n).read t)
      ((Operand.mem (rdi.read t) : Operand n).read t)).ZF

/-- `repneCmpsSpec` with an FS/GS segment override whose base is `base` (`cmpsSegSpec`,
`repneCmpsSegCont`). -/
def repneCmpsSegSpec (base : BitVec 64) (n : Nat) (t : RamState) : RamState :=
  if repneCmpsSegCont base n t then
    { rcx.write (cmpsSegSpec base n t) (rcx.read t - 1) with
      Repeat_String_Operation := true, RFLAGS := t.RFLAGS }
  else { rcx.write (cmpsSegSpec base n t) (rcx.read t - 1) with Repeat_String_Operation := false }

/--
One iteration of `REPE CMPS` of `n` bits with DF = 1 and RCX ≠ 0, from state `t`: one string
compare stepping down (`cmpsDownSpec`) and RCX decremented; if the instruction goes on
(`repeCmpsCont`, the operands at RSI and RDI before the step), the repeat flag is set and the flags
are put back as they were.
-/
def repeCmpsDownSpec (n : Nat) (t : RamState) : RamState :=
  if repeCmpsCont n t then
    { rcx.write (cmpsDownSpec n t) (rcx.read t - 1) with
      Repeat_String_Operation := true, RFLAGS := t.RFLAGS }
  else { rcx.write (cmpsDownSpec n t) (rcx.read t - 1) with Repeat_String_Operation := false }

/-- `repeCmpsDownSpec` for `REPNE CMPS` (`repneCmpsCont`). -/
def repneCmpsDownSpec (n : Nat) (t : RamState) : RamState :=
  if repneCmpsCont n t then
    { rcx.write (cmpsDownSpec n t) (rcx.read t - 1) with
      Repeat_String_Operation := true, RFLAGS := t.RFLAGS }
  else { rcx.write (cmpsDownSpec n t) (rcx.read t - 1) with Repeat_String_Operation := false }

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem selectCompareMemoryOrder_run [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (seg₁ : Segment) (src : BitVec 64)
    (seg₂ : Segment) (dst : BitVec 64) (u : RamState) :
    ∃ b, (Select_Compare_Memory_Order (n : Int) seg₁ src seg₂ dst).run u = (.ok b, u) := by
  have hc := hcm.1 ⟨n, seg₁, src, seg₂, dst⟩ u (by
    simp only [Prelude.Bindings.CompareMemory.orderContract,
      Prelude.Bindings.CompareMemory.supportedOperandSize]
    omega)
  dsimp only at hc
  revert hc
  cases hb : (inst.compareMemory (σ := Ram)).order.call (n : Int) seg₁ src seg₂ dst u with
  | error e =>
    intro hc
    change False at hc
    exact hc.elim
  | ok b =>
    intro _
    refine ⟨b, ?_⟩
    unfold Select_Compare_Memory_Order
    rw [assert_of_true (by rcases hn with rfl | rfl | rfl | rfl <;> decide), pure_bind]
    rw [specM_bind_run _ _ (get_run u)]
    apply specM_liftNoSourceException_run
    erw [hb]
    rfl

theorem emulateCompareMemoryRead_run_seg [Bindings] (u : RamState) (h : DataReady u) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (a lin b : BitVec 64) (seg seg' : Segment)
    (hsa : SegAccess seg a lin) (ha : MemReadable u lin (n / 8)) :
    (Emulate_Compare_Memory_Read (n : Int) seg a seg' b).run u =
      (.ok ((Operand.mem lin : Operand n).read u), dataAccess u "load") := by
  have hr := logicalMemRead_run_seg u h seg a lin hsa n hn .Memory_Read (.inl rfl) ha.low ha.mem
  unfold Emulate_Compare_Memory_Read
  rw [assert_of_true (by rcases hn with rfl | rfl | rfl | rfl <;> decide), pure_bind]
  exact specM_tryCatch_run _ _ hr

theorem emulateCompareMemoryRead_run [Bindings] (u : RamState) (h : DataReady u) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (a b : BitVec 64) (seg : Segment)
    (ha : MemReadable u a (n / 8)) :
    (Emulate_Compare_Memory_Read (n : Int) (flatData false) a seg b).run u =
      (.ok ((Operand.mem a : Operand n).read u), dataAccess u "load") :=
  emulateCompareMemoryRead_run_seg u h n hn a a b _ seg (SegAccess.flat false a) ha

theorem emulateCompareMemoryOperands_run_seg [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (u : RamState) (h : DataReady u) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (seg₁ seg₂ : Segment) (src dst lin₁ lin₂ : BitVec 64) (hs₁ : SegAccess seg₁ src lin₁)
    (hs₂ : SegAccess seg₂ dst lin₂) (hsrc : MemReadable u lin₁ (n / 8))
    (hdst : MemReadable u lin₂ (n / 8)) :
    (Emulate_Compare_Memory_Operands (n : Int) seg₁ src seg₂ dst).run u =
      (.ok ((Operand.mem lin₁ : Operand n).read u, (Operand.mem lin₂ : Operand n).read u),
        dataAccess (dataAccess u "load") "load") := by
  obtain ⟨b, hb⟩ := selectCompareMemoryOrder_run hcm n hn seg₁ src seg₂ dst u
  have hr (seg : Segment) (a lin : BitVec 64) (hs : SegAccess seg a lin)
      (ha : MemReadable u lin (n / 8)) :=
    logicalMemRead_run_seg (dataAccess u "load") (h.dataAccess _) seg a lin hs n hn .Memory_Read
      (.inl rfl) ha.low ha.mem
  unfold Emulate_Compare_Memory_Operands
  rw [assert_of_true (by rcases hn with rfl | rfl | rfl | rfl <;> decide), pure_bind]
  refine (specM_bind_run _ _ hb).trans ?_
  unfold Emulate_Compare_Memory_Transfer
  rw [assert_of_true (by rcases hn with rfl | rfl | rfl | rfl <;> decide), pure_bind]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _
      (emulateCompareMemoryRead_run_seg u h n hn src lin₁ dst _ _ hs₁ hsrc)).trans ?_
    refine (specM_bind_run _ _ (hr seg₂ dst lin₂ hs₂ hdst)).trans ?_
    rfl
  · simp only [↓reduceIte]
    refine (specM_bind_run _ _
      (emulateCompareMemoryRead_run_seg u h n hn dst lin₂ src _ _ hs₂ hdst)).trans ?_
    refine (specM_bind_run _ _ (hr seg₁ src lin₁ hs₁ hsrc)).trans ?_
    rfl

theorem emulateCompareMemoryOperands_run [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (u : RamState) (h : DataReady u) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (src dst : BitVec 64) (hsrc : MemReadable u src (n / 8)) (hdst : MemReadable u dst (n / 8)) :
    (Emulate_Compare_Memory_Operands (n : Int) (flatData false) src (flatData false) dst).run u =
      (.ok ((Operand.mem src : Operand n).read u, (Operand.mem dst : Operand n).read u),
        dataAccess (dataAccess u "load") "load") :=
  emulateCompareMemoryOperands_run_seg hcm u h n hn _ _ src dst src dst (SegAccess.flat false src)
    (SegAccess.flat false dst) hsrc hdst

theorem compare_string_operation [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (h : DataReady t) (hmode : In64BitMode t) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (ctx : Instruction_Context)
    (hseg : ctx.seg_prefix_present = false) (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hsrc : MemReadable t (rsi.read t) (n / 8))
    (hdst : MemReadable t (rdi.read t) (n / 8)) :
    (X86.Instructions.Operations.COMPARE_STRING (n : Int) ctx).run t = (.ok (), cmpsSpec n t) := by
  have hcmp := fun (u : RamState) (x y : BitVec n) => cmp_operation u n hn x y
  have hem := emulateCompareMemoryOperands_run hcm t h n hn (rsi.read t) (rdi.read t) hsrc hdst
  have hges : ∀ seg, Get_Effective_Segment ctx seg = .ok (nullDataSegment seg) :=
    fun seg => getEffectiveSegment_run ctx seg hseg hm64
  have haddr : (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run t =
      (.ok 64, t) := addressSize_run ctx hm64 hasz t
  unfold X86.Instructions.Operations.COMPARE_STRING
  simp only [hges]
  rcases hn with rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, pure_bind] at hem ⊢
    refine (specM_bind_run _ _ haddr).trans ?_
    rw [specM_bind_run _ _ (get_run t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ hmode).trans ?_
    simp only [↓reduceIte]
    rw [specM_bind_run _ _ (get_run t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    simp (config := { decide := true }) only [assert_of_true, pure_bind]
    refine (specM_bind_run _ _ (rsiSlice_run t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    refine (specM_bind_run _ _ (rdiSlice_run t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    rw [hds, hes]
    refine (specM_bind_run _ _ hem).trans ?_
    refine (specM_bind_run _ _ (hcmp _ _ _)).trans ?_
    refine (specM_bind_run _ _ (directionFlag_run _ ?_)).trans ?_
    · exact DirectionFlagClear.store hdf _
    simp only [beq_self_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (rsiSlice_run _)).trans ?_
    refine (specM_bind_run _ _ (addInt64_run _ _ _)).trans ?_
    refine (specM_bind_run _ _ (writeRSI64_run _ _)).trans ?_
    refine (specM_bind_run _ _ (rdiSlice_run _)).trans ?_
    refine (specM_bind_run _ _ (addInt64_run _ _ _)).trans ?_
    refine (writeRDI64_run _ _).trans ?_
    simp only [cmpsSpec, Operand.read_setFlags, Operand.read_reg_dataAccess, ofInt_div8,
      Operand.read_write_reg_of_ne _ (show (6 : BitVec 5) ≠ 7 by decide)]

theorem compare_string_once [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (hlock : ctx.lock_prefix_present = false) (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true) (hasz : ctx.asz_prefix_present = false)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hrep : t.Repeat_String_Operation = false)
    (hsrc : MemReadable t (rsi.read t) (n / 8)) (hdst : MemReadable t (rdi.read t) (n / 8)) :
    (X86.Instructions.Compare_String ip ctx (n : Int) false true).run t =
      (.ok (), cmpsSpec n { t with Next_IP := ip }) := by
  have hu : { { t with Next_IP := ip } with Repeat_String_Operation := false } =
      { t with Next_IP := ip } := by
    have : ∀ b, t.Repeat_String_Operation = b →
        { { t with Next_IP := ip } with Repeat_String_Operation := b } =
          { t with Next_IP := ip } := by
      rintro b rfl; rfl
    exact this _ hrep
  have hop := compare_string_operation hcm { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) n hn ctx hseg hm64 hasz hds hes hdf (hsrc.of_external_eq rfl)
    (hdst.of_external_eq rfl)
  have haddr (u : RamState) :
      (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run u = (.ok 64, u) :=
    addressSize_run ctx hm64 hasz u
  unfold X86.Instructions.Compare_String
  rw [assert_of_true (by rcases hn with rfl | rfl | rfl | rfl <;> decide), pure_bind]
  simp only [hlock, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  refine (specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false }))
    _ (s := { t with Next_IP := ip }) (t := { t with Next_IP := ip }) (value := PUnit.unit)
    ?_).trans ?_
  · change (Except.ok (), { { t with Next_IP := ip } with Repeat_String_Operation := false }) = _
    rw [hu]
  refine (specM_bind_run _ _ (haddr _)).trans ?_
  simp (config := { decide := true }) only [assert_of_true, pure_bind]
  refine (specM_bind_run _ _ (rcxSlice_run _)).trans ?_
  refine (specM_bind_run _ _ rfl).trans ?_
  simp only [HAnd.hAnd, AndOp.and, strictAnd, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ (get_run _)]
  refine (specM_bind_run _ _ hop).trans ?_
  rfl

theorem compare_string_operation_seg [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (h : DataReady t) (hmode : In64BitMode t) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (ctx : Instruction_Context)
    (hseg : ctx.seg_prefix_present = true) (hsr : SegReady ctx.segment)
    (hm64 : ctx.is_mode64 = true) (hasz : ctx.asz_prefix_present = false)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hsrc : MemReadable t (segBase ctx.segment + rsi.read t) (n / 8))
    (hdst : MemReadable t (rdi.read t) (n / 8)) :
    (X86.Instructions.Operations.COMPARE_STRING (n : Int) ctx).run t =
      (.ok (), cmpsSegSpec (segBase ctx.segment) n t) := by
  have hcmp := fun (u : RamState) (x y : BitVec n) => cmp_operation u n hn x y
  have hem := emulateCompareMemoryOperands_run_seg hcm t h n hn ctx.segment (flatData false)
    (rsi.read t) (rdi.read t) _ _ (hsr.access _) (SegAccess.flat false _) hsrc hdst
  have hges : ∀ seg, Get_Effective_Segment ctx seg = .ok ctx.segment :=
    fun seg => getEffectiveSegment_run_of_seg ctx seg hseg
  have haddr : (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run t =
      (.ok 64, t) := addressSize_run ctx hm64 hasz t
  unfold X86.Instructions.Operations.COMPARE_STRING
  simp only [hges]
  rcases hn with rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, pure_bind] at hem ⊢
    refine (specM_bind_run _ _ haddr).trans ?_
    rw [specM_bind_run _ _ (get_run t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ hmode).trans ?_
    simp only [↓reduceIte]
    rw [specM_bind_run _ _ (get_run t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    simp (config := { decide := true }) only [assert_of_true, pure_bind]
    refine (specM_bind_run _ _ (rsiSlice_run t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    refine (specM_bind_run _ _ (rdiSlice_run t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    rw [hes]
    refine (specM_bind_run _ _ hem).trans ?_
    refine (specM_bind_run _ _ (hcmp _ _ _)).trans ?_
    refine (specM_bind_run _ _ (directionFlag_run _ ?_)).trans ?_
    · exact DirectionFlagClear.store hdf _
    simp only [beq_self_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (rsiSlice_run _)).trans ?_
    refine (specM_bind_run _ _ (addInt64_run _ _ _)).trans ?_
    refine (specM_bind_run _ _ (writeRSI64_run _ _)).trans ?_
    refine (specM_bind_run _ _ (rdiSlice_run _)).trans ?_
    refine (specM_bind_run _ _ (addInt64_run _ _ _)).trans ?_
    refine (writeRDI64_run _ _).trans ?_
    simp only [cmpsSegSpec, Operand.read_setFlags, Operand.read_reg_dataAccess, ofInt_div8,
      Operand.read_write_reg_of_ne _ (show (6 : BitVec 5) ≠ 7 by decide)]

theorem compare_string_once_seg [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (hlock : ctx.lock_prefix_present = false) (hseg : ctx.seg_prefix_present = true)
    (hsr : SegReady ctx.segment) (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hrep : t.Repeat_String_Operation = false)
    (hsrc : MemReadable t (segBase ctx.segment + rsi.read t) (n / 8))
    (hdst : MemReadable t (rdi.read t) (n / 8)) :
    (X86.Instructions.Compare_String ip ctx (n : Int) false true).run t =
      (.ok (), cmpsSegSpec (segBase ctx.segment) n { t with Next_IP := ip }) := by
  have hu : { { t with Next_IP := ip } with Repeat_String_Operation := false } =
      { t with Next_IP := ip } := by
    have : ∀ b, t.Repeat_String_Operation = b →
        { { t with Next_IP := ip } with Repeat_String_Operation := b } =
          { t with Next_IP := ip } := by
      rintro b rfl; rfl
    exact this _ hrep
  have hop := compare_string_operation_seg hcm { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) n hn ctx hseg hsr hm64 hasz hes hdf (hsrc.of_external_eq rfl)
    (hdst.of_external_eq rfl)
  have haddr (u : RamState) :
      (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run u = (.ok 64, u) :=
    addressSize_run ctx hm64 hasz u
  unfold X86.Instructions.Compare_String
  rw [assert_of_true (by rcases hn with rfl | rfl | rfl | rfl <;> decide), pure_bind]
  simp only [hlock, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  refine (specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false }))
    _ (s := { t with Next_IP := ip }) (t := { t with Next_IP := ip }) (value := PUnit.unit)
    ?_).trans ?_
  · change (Except.ok (), { { t with Next_IP := ip } with Repeat_String_Operation := false }) = _
    rw [hu]
  refine (specM_bind_run _ _ (haddr _)).trans ?_
  simp (config := { decide := true }) only [assert_of_true, pure_bind]
  refine (specM_bind_run _ _ (rcxSlice_run _)).trans ?_
  refine (specM_bind_run _ _ rfl).trans ?_
  simp only [HAnd.hAnd, AndOp.and, strictAnd, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ (get_run _)]
  refine (specM_bind_run _ _ hop).trans ?_
  rfl

open scoped X86.Runtime.Syntax in
theorem compare_string_repeat [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (hlock : ctx.lock_prefix_present = false) (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true) (hasz : ctx.asz_prefix_present = false)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : MemReadable t (rsi.read t) (n / 8)) (hdst : MemReadable t (rdi.read t) (n / 8)) :
    (X86.Instructions.Compare_String ip ctx (n : Int) true true).run t =
      (.ok (), repeCmpsSpec n { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hop := compare_string_operation hcm
    { t with Next_IP := ip, Repeat_String_Operation := false }
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl
      rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) n hn ctx hseg hm64 hasz hds hes hdf (hsrc.of_external_eq rfl)
    (hdst.of_external_eq rfl)
  have haddr (u : RamState) :
      (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run u = (.ok 64, u) :=
    addressSize_run ctx hm64 hasz u
  have hsub (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Subtract_int (n := 64) v 1) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#64), a) := rfl
  unfold X86.Instructions.Compare_String
  rw [assert_of_true (by rcases hn with rfl | rfl | rfl | rfl <;> decide), pure_bind]
  simp only [hlock, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false })) _
    (s := { t with Next_IP := ip }) rfl]
  refine (specM_bind_run _ _ (haddr _)).trans ?_
  simp (config := { decide := true }) only [assert_of_true, pure_bind]
  refine (specM_bind_run _ _ (rcxSlice_run _)).trans ?_
  refine (specM_bind_run _ _ (hzero _ _)).trans ?_
  have hz :
      (rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } == 0#64) = false := by
    simpa using hcount
  rw [hz, ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
  rw [specM_bind_run _ _ (get_run _)]
  refine (specM_bind_run _ _ hop).trans ?_
  refine (specM_bind_run _ _ (rcxSlice_run _)).trans ?_
  refine (specM_bind_run _ _ (hsub _ _)).trans ?_
  refine (specM_bind_run _ _ (writeRCX64_run _ _)).trans ?_
  refine (specM_bind_run _ _ (rcxSlice_run _)).trans ?_
  refine (specM_bind_run _ _ (hzero _ _)).trans ?_
  refine (specM_bind_run _ _ (show (RFLAGS.ZF : X86.Runtime.SpecM X86.Exception RamState
    (BitVec 1)).run _ = (.ok _, _) from rfl)).trans ?_
  generalize ht' : { t with Next_IP := ip, Repeat_String_Operation := false } = t'
  have hr : rcx.read (cmpsSpec n t') = rcx.read t' := by
    simp only [cmpsSpec]
    rw [Operand.read_write_reg_of_ne _ (by decide), Operand.read_write_reg_of_ne _ (by decide),
      Operand.read_setFlags, Operand.read_reg_dataAccess, Operand.read_reg_dataAccess]
  have hf : (cmpsSpec n t').RFLAGS = (cmpSpec ((Operand.mem (rsi.read t') : Operand n).read t')
      ((Operand.mem (rdi.read t') : Operand n).read t')).store t'.RFLAGS := rfl
  have hC : ((!(rcx.read (rcx.write (cmpsSpec n t') (rcx.read (cmpsSpec n t') - 1)) == 0#64)) &&&
      ((BitVec.extractLsb' (Int.toNat 6) (Int.toNat 1)
        (rcx.write (cmpsSpec n t') (rcx.read (cmpsSpec n t') - 1)).RFLAGS == 1) == true)) =
      repeCmpsCont n t' := by
    have hb (r : BitVec 64) : (BitVec.extractLsb' 6 1 r == 1) = r.getLsbD 6 :=
      extractLsb'_one_beq r 6
    rw [rcx_read_write, show (rcx.write (cmpsSpec n t') (rcx.read (cmpsSpec n t') - 1)).RFLAGS =
        (cmpsSpec n t').RFLAGS from rfl,
      show Int.toNat 6 = 6 from rfl, show Int.toNat 1 = 1 from rfl, hb, hf, hr]
    unfold repeCmpsCont
    rw [← StatusFlags.ofRFLAGS_store (cmpSpec _ _) t'.RFLAGS]
    show _ = (!(rcx.read t' - 1 == 0#64) && (StatusFlags.store _ t'.RFLAGS).getLsbD 6)
    cases (rcx.read t' - 1 == 0#64) <;> simp [HAnd.hAnd, AndOp.and, strictAnd]
  rw [hC, hr]
  unfold repeCmpsSpec
  cases repeCmpsCont n t' <;> rfl

open scoped X86.Runtime.Syntax in
theorem compare_string_repeat_seg [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (hlock : ctx.lock_prefix_present = false) (hseg : ctx.seg_prefix_present = true)
    (hsr : SegReady ctx.segment) (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : MemReadable t (segBase ctx.segment + rsi.read t) (n / 8))
    (hdst : MemReadable t (rdi.read t) (n / 8)) :
    (X86.Instructions.Compare_String ip ctx (n : Int) true true).run t =
      (.ok (), repeCmpsSegSpec (segBase ctx.segment) n
        { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hop := compare_string_operation_seg hcm
    { t with Next_IP := ip, Repeat_String_Operation := false }
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl
      rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) n hn ctx hseg hsr hm64 hasz hes hdf (hsrc.of_external_eq rfl)
    (hdst.of_external_eq rfl)
  have haddr (u : RamState) :
      (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run u = (.ok 64, u) :=
    addressSize_run ctx hm64 hasz u
  have hsub (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Subtract_int (n := 64) v 1) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#64), a) := rfl
  unfold X86.Instructions.Compare_String
  rw [assert_of_true (by rcases hn with rfl | rfl | rfl | rfl <;> decide), pure_bind]
  simp only [hlock, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false })) _
    (s := { t with Next_IP := ip }) rfl]
  refine (specM_bind_run _ _ (haddr _)).trans ?_
  simp (config := { decide := true }) only [assert_of_true, pure_bind]
  refine (specM_bind_run _ _ (rcxSlice_run _)).trans ?_
  refine (specM_bind_run _ _ (hzero _ _)).trans ?_
  have hz :
      (rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } == 0#64) = false := by
    simpa using hcount
  rw [hz, ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
  rw [specM_bind_run _ _ (get_run _)]
  refine (specM_bind_run _ _ hop).trans ?_
  refine (specM_bind_run _ _ (rcxSlice_run _)).trans ?_
  refine (specM_bind_run _ _ (hsub _ _)).trans ?_
  refine (specM_bind_run _ _ (writeRCX64_run _ _)).trans ?_
  refine (specM_bind_run _ _ (rcxSlice_run _)).trans ?_
  refine (specM_bind_run _ _ (hzero _ _)).trans ?_
  refine (specM_bind_run _ _ (show (RFLAGS.ZF : X86.Runtime.SpecM X86.Exception RamState
    (BitVec 1)).run _ = (.ok _, _) from rfl)).trans ?_
  generalize ht' : { t with Next_IP := ip, Repeat_String_Operation := false } = t'
  have hr : rcx.read (cmpsSegSpec (segBase ctx.segment) n t') = rcx.read t' := by
    simp only [cmpsSegSpec]
    rw [Operand.read_write_reg_of_ne _ (by decide), Operand.read_write_reg_of_ne _ (by decide),
      Operand.read_setFlags, Operand.read_reg_dataAccess, Operand.read_reg_dataAccess]
  have hf : (cmpsSegSpec (segBase ctx.segment) n t').RFLAGS =
      (cmpSpec ((Operand.mem (segBase ctx.segment + rsi.read t') : Operand n).read t')
      ((Operand.mem (rdi.read t') : Operand n).read t')).store t'.RFLAGS := rfl
  have hC : ((!(rcx.read (rcx.write (cmpsSegSpec (segBase ctx.segment) n t') (rcx.read (cmpsSegSpec (segBase ctx.segment) n t') - 1)) == 0#64)) &&&
      ((BitVec.extractLsb' (Int.toNat 6) (Int.toNat 1)
        (rcx.write (cmpsSegSpec (segBase ctx.segment) n t') (rcx.read (cmpsSegSpec (segBase ctx.segment) n t') - 1)).RFLAGS == 1) == true)) =
      repeCmpsSegCont (segBase ctx.segment) n t' := by
    have hb (r : BitVec 64) : (BitVec.extractLsb' 6 1 r == 1) = r.getLsbD 6 :=
      extractLsb'_one_beq r 6
    rw [rcx_read_write, show (rcx.write (cmpsSegSpec (segBase ctx.segment) n t') (rcx.read (cmpsSegSpec (segBase ctx.segment) n t') - 1)).RFLAGS =
        (cmpsSegSpec (segBase ctx.segment) n t').RFLAGS from rfl,
      show Int.toNat 6 = 6 from rfl, show Int.toNat 1 = 1 from rfl, hb, hf, hr]
    unfold repeCmpsSegCont
    rw [← StatusFlags.ofRFLAGS_store (cmpSpec _ _) t'.RFLAGS]
    show _ = (!(rcx.read t' - 1 == 0#64) && (StatusFlags.store _ t'.RFLAGS).getLsbD 6)
    cases (rcx.read t' - 1 == 0#64) <;> simp [HAnd.hAnd, AndOp.and, strictAnd]
  rw [hC, hr]
  unfold repeCmpsSegSpec
  cases repeCmpsSegCont (segBase ctx.segment) n t' <;> rfl

open scoped X86.Runtime.Syntax in
theorem compare_string_repeat_zero [Bindings] (t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (hlock : ctx.lock_prefix_present = false) (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false) (hcount : rcx.read t = 0) :
    (X86.Instructions.Compare_String ip ctx (n : Int) true true).run t =
      (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have haddr (u : RamState) :
      (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run u = (.ok 64, u) :=
    addressSize_run ctx hm64 hasz u
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#64), a) := rfl
  unfold X86.Instructions.Compare_String
  rw [assert_of_true (by rcases hn with rfl | rfl | rfl | rfl <;> decide), pure_bind]
  simp only [hlock, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false })) _
    (s := { t with Next_IP := ip }) rfl]
  refine (specM_bind_run _ _ (haddr _)).trans ?_
  simp (config := { decide := true }) only [assert_of_true, pure_bind]
  refine (specM_bind_run _ _ (rcxSlice_run _)).trans ?_
  refine (specM_bind_run _ _ (hzero _ _)).trans ?_
  have hz :
      (rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } == 0#64) = true := by
    simpa using hcount
  rw [hz, ite_eq_left_of_eq_true _ _ (eq_true (by decide))]
  rfl

open scoped X86.Runtime.Syntax in
theorem compare_string_repeat_ne [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (hlock : ctx.lock_prefix_present = false) (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true) (hasz : ctx.asz_prefix_present = false)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : MemReadable t (rsi.read t) (n / 8)) (hdst : MemReadable t (rdi.read t) (n / 8)) :
    (X86.Instructions.Compare_String ip ctx (n : Int) true false).run t =
      (.ok (), repneCmpsSpec n { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hop := compare_string_operation hcm
    { t with Next_IP := ip, Repeat_String_Operation := false }
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl
      rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) n hn ctx hseg hm64 hasz hds hes hdf (hsrc.of_external_eq rfl)
    (hdst.of_external_eq rfl)
  have haddr (u : RamState) :
      (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run u = (.ok 64, u) :=
    addressSize_run ctx hm64 hasz u
  have hsub (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Subtract_int (n := 64) v 1) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#64), a) := rfl
  unfold X86.Instructions.Compare_String
  rw [assert_of_true (by rcases hn with rfl | rfl | rfl | rfl <;> decide), pure_bind]
  simp only [hlock, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false })) _
    (s := { t with Next_IP := ip }) rfl]
  refine (specM_bind_run _ _ (haddr _)).trans ?_
  simp (config := { decide := true }) only [assert_of_true, pure_bind]
  refine (specM_bind_run _ _ (rcxSlice_run _)).trans ?_
  refine (specM_bind_run _ _ (hzero _ _)).trans ?_
  have hz :
      (rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } == 0#64) = false := by
    simpa using hcount
  rw [hz, ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
  rw [specM_bind_run _ _ (get_run _)]
  refine (specM_bind_run _ _ hop).trans ?_
  refine (specM_bind_run _ _ (rcxSlice_run _)).trans ?_
  refine (specM_bind_run _ _ (hsub _ _)).trans ?_
  refine (specM_bind_run _ _ (writeRCX64_run _ _)).trans ?_
  refine (specM_bind_run _ _ (rcxSlice_run _)).trans ?_
  refine (specM_bind_run _ _ (hzero _ _)).trans ?_
  refine (specM_bind_run _ _ (show (RFLAGS.ZF : X86.Runtime.SpecM X86.Exception RamState
    (BitVec 1)).run _ = (.ok _, _) from rfl)).trans ?_
  generalize ht' : { t with Next_IP := ip, Repeat_String_Operation := false } = t'
  have hr : rcx.read (cmpsSpec n t') = rcx.read t' := by
    simp only [cmpsSpec]
    rw [Operand.read_write_reg_of_ne _ (by decide), Operand.read_write_reg_of_ne _ (by decide),
      Operand.read_setFlags, Operand.read_reg_dataAccess, Operand.read_reg_dataAccess]
  have hf : (cmpsSpec n t').RFLAGS = (cmpSpec ((Operand.mem (rsi.read t') : Operand n).read t')
      ((Operand.mem (rdi.read t') : Operand n).read t')).store t'.RFLAGS := rfl
  have hC : ((!(rcx.read (rcx.write (cmpsSpec n t') (rcx.read (cmpsSpec n t') - 1)) == 0#64)) &&&
      ((BitVec.extractLsb' (Int.toNat 6) (Int.toNat 1)
        (rcx.write (cmpsSpec n t') (rcx.read (cmpsSpec n t') - 1)).RFLAGS == 1) == false)) =
      repneCmpsCont n t' := by
    have hb (r : BitVec 64) : (BitVec.extractLsb' 6 1 r == 1) = r.getLsbD 6 :=
      extractLsb'_one_beq r 6
    rw [rcx_read_write, show (rcx.write (cmpsSpec n t') (rcx.read (cmpsSpec n t') - 1)).RFLAGS =
        (cmpsSpec n t').RFLAGS from rfl,
      show Int.toNat 6 = 6 from rfl, show Int.toNat 1 = 1 from rfl, hb, hf, hr]
    unfold repneCmpsCont
    rw [← StatusFlags.ofRFLAGS_store (cmpSpec _ _) t'.RFLAGS]
    show _ = (!(rcx.read t' - 1 == 0#64) && !(StatusFlags.store _ t'.RFLAGS).getLsbD 6)
    cases (rcx.read t' - 1 == 0#64) <;> simp [HAnd.hAnd, AndOp.and, strictAnd]
  rw [hC, hr]
  unfold repneCmpsSpec
  cases repneCmpsCont n t' <;> rfl

open scoped X86.Runtime.Syntax in
theorem compare_string_repeat_ne_seg [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (hlock : ctx.lock_prefix_present = false) (hseg : ctx.seg_prefix_present = true)
    (hsr : SegReady ctx.segment) (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : MemReadable t (segBase ctx.segment + rsi.read t) (n / 8))
    (hdst : MemReadable t (rdi.read t) (n / 8)) :
    (X86.Instructions.Compare_String ip ctx (n : Int) true false).run t =
      (.ok (), repneCmpsSegSpec (segBase ctx.segment) n
        { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hop := compare_string_operation_seg hcm
    { t with Next_IP := ip, Repeat_String_Operation := false }
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl
      rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) n hn ctx hseg hsr hm64 hasz hes hdf (hsrc.of_external_eq rfl)
    (hdst.of_external_eq rfl)
  have haddr (u : RamState) :
      (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run u = (.ok 64, u) :=
    addressSize_run ctx hm64 hasz u
  have hsub (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Subtract_int (n := 64) v 1) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#64), a) := rfl
  unfold X86.Instructions.Compare_String
  rw [assert_of_true (by rcases hn with rfl | rfl | rfl | rfl <;> decide), pure_bind]
  simp only [hlock, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false })) _
    (s := { t with Next_IP := ip }) rfl]
  refine (specM_bind_run _ _ (haddr _)).trans ?_
  simp (config := { decide := true }) only [assert_of_true, pure_bind]
  refine (specM_bind_run _ _ (rcxSlice_run _)).trans ?_
  refine (specM_bind_run _ _ (hzero _ _)).trans ?_
  have hz :
      (rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } == 0#64) = false := by
    simpa using hcount
  rw [hz, ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
  rw [specM_bind_run _ _ (get_run _)]
  refine (specM_bind_run _ _ hop).trans ?_
  refine (specM_bind_run _ _ (rcxSlice_run _)).trans ?_
  refine (specM_bind_run _ _ (hsub _ _)).trans ?_
  refine (specM_bind_run _ _ (writeRCX64_run _ _)).trans ?_
  refine (specM_bind_run _ _ (rcxSlice_run _)).trans ?_
  refine (specM_bind_run _ _ (hzero _ _)).trans ?_
  refine (specM_bind_run _ _ (show (RFLAGS.ZF : X86.Runtime.SpecM X86.Exception RamState
    (BitVec 1)).run _ = (.ok _, _) from rfl)).trans ?_
  generalize ht' : { t with Next_IP := ip, Repeat_String_Operation := false } = t'
  have hr : rcx.read (cmpsSegSpec (segBase ctx.segment) n t') = rcx.read t' := by
    simp only [cmpsSegSpec]
    rw [Operand.read_write_reg_of_ne _ (by decide), Operand.read_write_reg_of_ne _ (by decide),
      Operand.read_setFlags, Operand.read_reg_dataAccess, Operand.read_reg_dataAccess]
  have hf : (cmpsSegSpec (segBase ctx.segment) n t').RFLAGS =
      (cmpSpec ((Operand.mem (segBase ctx.segment + rsi.read t') : Operand n).read t')
      ((Operand.mem (rdi.read t') : Operand n).read t')).store t'.RFLAGS := rfl
  have hC : ((!(rcx.read (rcx.write (cmpsSegSpec (segBase ctx.segment) n t') (rcx.read (cmpsSegSpec (segBase ctx.segment) n t') - 1)) == 0#64)) &&&
      ((BitVec.extractLsb' (Int.toNat 6) (Int.toNat 1)
        (rcx.write (cmpsSegSpec (segBase ctx.segment) n t') (rcx.read (cmpsSegSpec (segBase ctx.segment) n t') - 1)).RFLAGS == 1) == false)) =
      repneCmpsSegCont (segBase ctx.segment) n t' := by
    have hb (r : BitVec 64) : (BitVec.extractLsb' 6 1 r == 1) = r.getLsbD 6 :=
      extractLsb'_one_beq r 6
    rw [rcx_read_write, show (rcx.write (cmpsSegSpec (segBase ctx.segment) n t') (rcx.read (cmpsSegSpec (segBase ctx.segment) n t') - 1)).RFLAGS =
        (cmpsSegSpec (segBase ctx.segment) n t').RFLAGS from rfl,
      show Int.toNat 6 = 6 from rfl, show Int.toNat 1 = 1 from rfl, hb, hf, hr]
    unfold repneCmpsSegCont
    rw [← StatusFlags.ofRFLAGS_store (cmpSpec _ _) t'.RFLAGS]
    show _ = (!(rcx.read t' - 1 == 0#64) && !(StatusFlags.store _ t'.RFLAGS).getLsbD 6)
    cases (rcx.read t' - 1 == 0#64) <;> simp [HAnd.hAnd, AndOp.and, strictAnd]
  rw [hC, hr]
  unfold repneCmpsSegSpec
  cases repneCmpsSegCont (segBase ctx.segment) n t' <;> rfl

open scoped X86.Runtime.Syntax in
theorem compare_string_repeat_ne_zero [Bindings] (t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (hlock : ctx.lock_prefix_present = false) (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false) (hcount : rcx.read t = 0) :
    (X86.Instructions.Compare_String ip ctx (n : Int) true false).run t =
      (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have haddr (u : RamState) :
      (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run u = (.ok 64, u) :=
    addressSize_run ctx hm64 hasz u
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#64), a) := rfl
  unfold X86.Instructions.Compare_String
  rw [assert_of_true (by rcases hn with rfl | rfl | rfl | rfl <;> decide), pure_bind]
  simp only [hlock, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false })) _
    (s := { t with Next_IP := ip }) rfl]
  refine (specM_bind_run _ _ (haddr _)).trans ?_
  simp (config := { decide := true }) only [assert_of_true, pure_bind]
  refine (specM_bind_run _ _ (rcxSlice_run _)).trans ?_
  refine (specM_bind_run _ _ (hzero _ _)).trans ?_
  have hz :
      (rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } == 0#64) = true := by
    simpa using hcount
  rw [hz, ite_eq_left_of_eq_true _ _ (eq_true (by decide))]
  rfl

theorem compare_string_operation_down [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (h : DataReady t) (hmode : In64BitMode t) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (ctx : Instruction_Context)
    (hseg : ctx.seg_prefix_present = false) (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS) (hsrc : MemReadable t (rsi.read t) (n / 8))
    (hdst : MemReadable t (rdi.read t) (n / 8)) :
    (X86.Instructions.Operations.COMPARE_STRING (n : Int) ctx).run t =
      (.ok (), cmpsDownSpec n t) := by
  have hcmp := fun (u : RamState) (x y : BitVec n) => cmp_operation u n hn x y
  have hem := emulateCompareMemoryOperands_run hcm t h n hn (rsi.read t) (rdi.read t) hsrc hdst
  have hges : ∀ seg, Get_Effective_Segment ctx seg = .ok (nullDataSegment seg) :=
    fun seg => getEffectiveSegment_run ctx seg hseg hm64
  have haddr : (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run t =
      (.ok 64, t) := addressSize_run ctx hm64 hasz t
  unfold X86.Instructions.Operations.COMPARE_STRING
  simp only [hges]
  rcases hn with rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, pure_bind] at hem ⊢
    refine (specM_bind_run _ _ haddr).trans ?_
    rw [specM_bind_run _ _ (get_run t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ hmode).trans ?_
    simp only [↓reduceIte]
    rw [specM_bind_run _ _ (get_run t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    simp (config := { decide := true }) only [assert_of_true, pure_bind]
    refine (specM_bind_run _ _ (rsiSlice_run t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    refine (specM_bind_run _ _ (rdiSlice_run t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    rw [hds, hes]
    refine (specM_bind_run _ _ hem).trans ?_
    refine (specM_bind_run _ _ (hcmp _ _ _)).trans ?_
    refine (specM_bind_run _ _ (directionFlagSet_run _ ?_)).trans ?_
    · exact DirectionFlagSet.store hdf _
    simp (config := { decide := true }) only [↓reduceIte]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (rsiSlice_run _)).trans ?_
    refine (specM_bind_run _ _ (addInt64_run _ _ _)).trans ?_
    refine (specM_bind_run _ _ (writeRSI64_run _ _)).trans ?_
    refine (specM_bind_run _ _ (rdiSlice_run _)).trans ?_
    refine (specM_bind_run _ _ (addInt64_run _ _ _)).trans ?_
    refine (writeRDI64_run _ _).trans ?_
    simp only [cmpsDownSpec, Operand.read_setFlags, Operand.read_reg_dataAccess, ofInt_neg_div8,
      ← BitVec.sub_eq_add_neg,
      Operand.read_write_reg_of_ne _ (show (6 : BitVec 5) ≠ 7 by decide)]

theorem compare_string_once_down [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (hlock : ctx.lock_prefix_present = false) (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true) (hasz : ctx.asz_prefix_present = false)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS) (hrep : t.Repeat_String_Operation = false)
    (hsrc : MemReadable t (rsi.read t) (n / 8)) (hdst : MemReadable t (rdi.read t) (n / 8)) :
    (X86.Instructions.Compare_String ip ctx (n : Int) false true).run t =
      (.ok (), cmpsDownSpec n { t with Next_IP := ip }) := by
  have hu : { { t with Next_IP := ip } with Repeat_String_Operation := false } =
      { t with Next_IP := ip } := by
    have : ∀ b, t.Repeat_String_Operation = b →
        { { t with Next_IP := ip } with Repeat_String_Operation := b } =
          { t with Next_IP := ip } := by
      rintro b rfl; rfl
    exact this _ hrep
  have hop := compare_string_operation_down hcm { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) n hn ctx hseg hm64 hasz hds hes hdf (hsrc.of_external_eq rfl)
    (hdst.of_external_eq rfl)
  have haddr (u : RamState) :
      (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run u = (.ok 64, u) :=
    addressSize_run ctx hm64 hasz u
  unfold X86.Instructions.Compare_String
  rw [assert_of_true (by rcases hn with rfl | rfl | rfl | rfl <;> decide), pure_bind]
  simp only [hlock, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  refine (specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false }))
    _ (s := { t with Next_IP := ip }) (t := { t with Next_IP := ip }) (value := PUnit.unit)
    ?_).trans ?_
  · change (Except.ok (), { { t with Next_IP := ip } with Repeat_String_Operation := false }) = _
    rw [hu]
  refine (specM_bind_run _ _ (haddr _)).trans ?_
  simp (config := { decide := true }) only [assert_of_true, pure_bind]
  refine (specM_bind_run _ _ (rcxSlice_run _)).trans ?_
  refine (specM_bind_run _ _ rfl).trans ?_
  simp only [HAnd.hAnd, AndOp.and, strictAnd, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ (get_run _)]
  refine (specM_bind_run _ _ hop).trans ?_
  rfl

theorem compare_string_operation_down_seg [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (h : DataReady t) (hmode : In64BitMode t) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (ctx : Instruction_Context)
    (hseg : ctx.seg_prefix_present = true) (hsr : SegReady ctx.segment)
    (hm64 : ctx.is_mode64 = true) (hasz : ctx.asz_prefix_present = false)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS)
    (hsrc : MemReadable t (segBase ctx.segment + rsi.read t) (n / 8))
    (hdst : MemReadable t (rdi.read t) (n / 8)) :
    (X86.Instructions.Operations.COMPARE_STRING (n : Int) ctx).run t =
      (.ok (), cmpsDownSegSpec (segBase ctx.segment) n t) := by
  have hcmp := fun (u : RamState) (x y : BitVec n) => cmp_operation u n hn x y
  have hem := emulateCompareMemoryOperands_run_seg hcm t h n hn ctx.segment (flatData false)
    (rsi.read t) (rdi.read t) _ _ (hsr.access _) (SegAccess.flat false _) hsrc hdst
  have hges : ∀ seg, Get_Effective_Segment ctx seg = .ok ctx.segment :=
    fun seg => getEffectiveSegment_run_of_seg ctx seg hseg
  have haddr : (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run t =
      (.ok 64, t) := addressSize_run ctx hm64 hasz t
  unfold X86.Instructions.Operations.COMPARE_STRING
  simp only [hges]
  rcases hn with rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, pure_bind] at hem ⊢
    refine (specM_bind_run _ _ haddr).trans ?_
    rw [specM_bind_run _ _ (get_run t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ hmode).trans ?_
    simp only [↓reduceIte]
    rw [specM_bind_run _ _ (get_run t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    simp (config := { decide := true }) only [assert_of_true, pure_bind]
    refine (specM_bind_run _ _ (rsiSlice_run t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    refine (specM_bind_run _ _ (rdiSlice_run t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    rw [hes]
    refine (specM_bind_run _ _ hem).trans ?_
    refine (specM_bind_run _ _ (hcmp _ _ _)).trans ?_
    refine (specM_bind_run _ _ (directionFlagSet_run _ ?_)).trans ?_
    · exact DirectionFlagSet.store hdf _
    simp (config := { decide := true }) only [↓reduceIte]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (rsiSlice_run _)).trans ?_
    refine (specM_bind_run _ _ (addInt64_run _ _ _)).trans ?_
    refine (specM_bind_run _ _ (writeRSI64_run _ _)).trans ?_
    refine (specM_bind_run _ _ (rdiSlice_run _)).trans ?_
    refine (specM_bind_run _ _ (addInt64_run _ _ _)).trans ?_
    refine (writeRDI64_run _ _).trans ?_
    simp only [cmpsDownSegSpec, Operand.read_setFlags, Operand.read_reg_dataAccess, ofInt_neg_div8,
      ← BitVec.sub_eq_add_neg,
      Operand.read_write_reg_of_ne _ (show (6 : BitVec 5) ≠ 7 by decide)]

theorem compare_string_once_down_seg [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (hlock : ctx.lock_prefix_present = false) (hseg : ctx.seg_prefix_present = true)
    (hsr : SegReady ctx.segment) (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS) (hrep : t.Repeat_String_Operation = false)
    (hsrc : MemReadable t (segBase ctx.segment + rsi.read t) (n / 8))
    (hdst : MemReadable t (rdi.read t) (n / 8)) :
    (X86.Instructions.Compare_String ip ctx (n : Int) false true).run t =
      (.ok (), cmpsDownSegSpec (segBase ctx.segment) n { t with Next_IP := ip }) := by
  have hu : { { t with Next_IP := ip } with Repeat_String_Operation := false } =
      { t with Next_IP := ip } := by
    have : ∀ b, t.Repeat_String_Operation = b →
        { { t with Next_IP := ip } with Repeat_String_Operation := b } =
          { t with Next_IP := ip } := by
      rintro b rfl; rfl
    exact this _ hrep
  have hop := compare_string_operation_down_seg hcm { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) n hn ctx hseg hsr hm64 hasz hes hdf (hsrc.of_external_eq rfl)
    (hdst.of_external_eq rfl)
  have haddr (u : RamState) :
      (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run u = (.ok 64, u) :=
    addressSize_run ctx hm64 hasz u
  unfold X86.Instructions.Compare_String
  rw [assert_of_true (by rcases hn with rfl | rfl | rfl | rfl <;> decide), pure_bind]
  simp only [hlock, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  refine (specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false }))
    _ (s := { t with Next_IP := ip }) (t := { t with Next_IP := ip }) (value := PUnit.unit)
    ?_).trans ?_
  · change (Except.ok (), { { t with Next_IP := ip } with Repeat_String_Operation := false }) = _
    rw [hu]
  refine (specM_bind_run _ _ (haddr _)).trans ?_
  simp (config := { decide := true }) only [assert_of_true, pure_bind]
  refine (specM_bind_run _ _ (rcxSlice_run _)).trans ?_
  refine (specM_bind_run _ _ rfl).trans ?_
  simp only [HAnd.hAnd, AndOp.and, strictAnd, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ (get_run _)]
  refine (specM_bind_run _ _ hop).trans ?_
  rfl

/-- In 64-bit mode with an address-size prefix (`67`), lean-x86's `Address_Size` is 32. -/
theorem addressSize32_run (ctx : Instruction_Context) (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = true) (s : RamState) :
    (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run s = (.ok 32, s) := by
  rw [addressSize_mode64_run ctx hm64, hasz]
  rfl

theorem compare_string_operation_a32 [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (h : DataReady t) (hmode : In64BitMode t) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (ctx : Instruction_Context)
    (hseg : ctx.seg_prefix_present = false) (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hsrc : MemReadable t (rsi.read t) (n / 8))
    (hdst : MemReadable t (rdi.read t) (n / 8)) (hsl : (rsi.read t).toNat + n / 8 < 2^32)
    (hdl : (rdi.read t).toNat + n / 8 < 2^32) :
    (X86.Instructions.Operations.COMPARE_STRING (n : Int) ctx).run t = (.ok (), cmpsSpec n t) := by
  have hcmp := fun (u : RamState) (x y : BitVec n) => cmp_operation u n hn x y
  have hem := emulateCompareMemoryOperands_run hcm t h n hn (rsi.read t) (rdi.read t) hsrc hdst
  have hges : ∀ seg, Get_Effective_Segment ctx seg = .ok (nullDataSegment seg) :=
    fun seg => getEffectiveSegment_run ctx seg hseg hm64
  have haddr : (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run t =
      (.ok 32, t) := addressSize32_run ctx hm64 hasz t
  have has : ((rsi.read t).setWidth 32).setWidth 64 = rsi.read t :=
    setWidth32_setWidth64_of_lt (by omega)
  have had : ((rdi.read t).setWidth 32).setWidth 64 = rdi.read t :=
    setWidth32_setWidth64_of_lt (by omega)
  unfold X86.Instructions.Operations.COMPARE_STRING
  simp only [hges]
  rcases hn with rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, pure_bind] at hem ⊢
    refine (specM_bind_run _ _ haddr).trans ?_
    rw [specM_bind_run _ _ (get_run t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ hmode).trans ?_
    simp only [↓reduceIte]
    rw [specM_bind_run _ _ (get_run t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    simp (config := { decide := true }) only [assert_of_true, pure_bind]
    refine (specM_bind_run _ _ (rsiSlice32_run t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend32_run _ _)).trans ?_
    refine (specM_bind_run _ _ (rdiSlice32_run t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend32_run _ _)).trans ?_
    rw [has, had, hds, hes]
    refine (specM_bind_run _ _ hem).trans ?_
    refine (specM_bind_run _ _ (hcmp _ _ _)).trans ?_
    refine (specM_bind_run _ _ (directionFlag_run _ ?_)).trans ?_
    · exact DirectionFlagClear.store hdf _
    simp only [beq_self_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (rsiSlice32_run _)).trans ?_
    refine (specM_bind_run _ _ (addInt32_run _ _ _)).trans ?_
    refine (specM_bind_run _ _ (writeRSI32_run _ _)).trans ?_
    refine (specM_bind_run _ _ (rdiSlice32_run _)).trans ?_
    refine (specM_bind_run _ _ (addInt32_run _ _ _)).trans ?_
    refine (writeRDI32_run _ _).trans ?_
    simp only [cmpsSpec, Operand.read_setFlags, Operand.read_reg_dataAccess, ofInt32_div8,
      Operand.read_write_reg_of_ne _ (show (6 : BitVec 5) ≠ 7 by decide)]
    rw [setWidth64_add_of_lt (by omega), setWidth64_add_of_lt (by omega)]

theorem compare_string_once_a32 [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (hlock : ctx.lock_prefix_present = false) (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true) (hasz : ctx.asz_prefix_present = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hrep : t.Repeat_String_Operation = false)
    (hsrc : MemReadable t (rsi.read t) (n / 8)) (hdst : MemReadable t (rdi.read t) (n / 8))
    (hsl : (rsi.read t).toNat + n / 8 < 2^32) (hdl : (rdi.read t).toNat + n / 8 < 2^32) :
    (X86.Instructions.Compare_String ip ctx (n : Int) false true).run t =
      (.ok (), cmpsSpec n { t with Next_IP := ip }) := by
  have hu : { { t with Next_IP := ip } with Repeat_String_Operation := false } =
      { t with Next_IP := ip } := by
    have : ∀ b, t.Repeat_String_Operation = b →
        { { t with Next_IP := ip } with Repeat_String_Operation := b } =
          { t with Next_IP := ip } := by
      rintro b rfl; rfl
    exact this _ hrep
  have hop := compare_string_operation_a32 hcm { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) n hn ctx hseg hm64 hasz hds hes hdf (hsrc.of_external_eq rfl)
    (hdst.of_external_eq rfl) hsl hdl
  have haddr (u : RamState) :
      (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run u = (.ok 32, u) :=
    addressSize32_run ctx hm64 hasz u
  unfold X86.Instructions.Compare_String
  rw [assert_of_true (by rcases hn with rfl | rfl | rfl | rfl <;> decide), pure_bind]
  simp only [hlock, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  refine (specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false }))
    _ (s := { t with Next_IP := ip }) (t := { t with Next_IP := ip }) (value := PUnit.unit)
    ?_).trans ?_
  · change (Except.ok (), { { t with Next_IP := ip } with Repeat_String_Operation := false }) = _
    rw [hu]
  refine (specM_bind_run _ _ (haddr _)).trans ?_
  simp (config := { decide := true }) only [assert_of_true, pure_bind]
  refine (specM_bind_run _ _ (rcxSlice32_run _)).trans ?_
  refine (specM_bind_run _ _ rfl).trans ?_
  simp only [HAnd.hAnd, AndOp.and, strictAnd, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ (get_run _)]
  refine (specM_bind_run _ _ hop).trans ?_
  rfl

open scoped X86.Runtime.Syntax in
theorem compare_string_repeat_a32 [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (hlock : ctx.lock_prefix_present = false) (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true) (hasz : ctx.asz_prefix_present = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : MemReadable t (rsi.read t) (n / 8)) (hdst : MemReadable t (rdi.read t) (n / 8))
    (hsl : (rsi.read t).toNat + n / 8 < 2^32) (hdl : (rdi.read t).toNat + n / 8 < 2^32)
    (hcl : (rcx.read t).toNat < 2^32) :
    (X86.Instructions.Compare_String ip ctx (n : Int) true true).run t =
      (.ok (), repeCmpsSpec n { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hop := compare_string_operation_a32 hcm
    { t with Next_IP := ip, Repeat_String_Operation := false }
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl
      rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) n hn ctx hseg hm64 hasz hds hes hdf (hsrc.of_external_eq rfl)
    (hdst.of_external_eq rfl) hsl hdl
  have haddr (u : RamState) :
      (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run u = (.ok 32, u) :=
    addressSize32_run ctx hm64 hasz u
  have hsub (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Subtract_int (n := 32) v 1) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 32)).run a = (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Is_Zero (size := 32) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#32), a) := rfl
  unfold X86.Instructions.Compare_String
  rw [assert_of_true (by rcases hn with rfl | rfl | rfl | rfl <;> decide), pure_bind]
  simp only [hlock, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false })) _
    (s := { t with Next_IP := ip }) rfl]
  refine (specM_bind_run _ _ (haddr _)).trans ?_
  simp (config := { decide := true }) only [assert_of_true, pure_bind]
  refine (specM_bind_run _ _ (rcxSlice32_run _)).trans ?_
  refine (specM_bind_run _ _ (hzero _ _)).trans ?_
  have hz : ((rcx.read { t with Next_IP := ip, Repeat_String_Operation := false }).setWidth 32 ==
      0#32) = false := by
    show ((rcx.read t).setWidth 32 == 0#32) = false
    rw [setWidth32_beq_zero_of_lt hcl]
    simpa using hcount
  rw [hz, ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
  rw [specM_bind_run _ _ (get_run _)]
  refine (specM_bind_run _ _ hop).trans ?_
  refine (specM_bind_run _ _ (rcxSlice32_run _)).trans ?_
  refine (specM_bind_run _ _ (hsub _ _)).trans ?_
  refine (specM_bind_run _ _ (writeRCX32_run _ _)).trans ?_
  refine (specM_bind_run _ _ (rcxSlice32_run _)).trans ?_
  refine (specM_bind_run _ _ (hzero _ _)).trans ?_
  refine (specM_bind_run _ _ (show (RFLAGS.ZF : X86.Runtime.SpecM X86.Exception RamState
    (BitVec 1)).run _ = (.ok _, _) from rfl)).trans ?_
  generalize ht' : { t with Next_IP := ip, Repeat_String_Operation := false } = t'
  have hcl' : (rcx.read t').toNat < 2^32 := by rw [← ht']; exact hcl
  have hc0 : rcx.read t' ≠ 0 := by rw [← ht']; exact hcount
  have hr : rcx.read (cmpsSpec n t') = rcx.read t' := by
    simp only [cmpsSpec]
    rw [Operand.read_write_reg_of_ne _ (by decide), Operand.read_write_reg_of_ne _ (by decide),
      Operand.read_setFlags, Operand.read_reg_dataAccess, Operand.read_reg_dataAccess]
  have hw : ((rcx.read (cmpsSpec n t')).setWidth 32 - 1).setWidth 64 = rcx.read t' - 1 := by
    rw [hr, setWidth64_sub_one_of_lt hcl' hc0]
  rw [hw]
  have hf : (cmpsSpec n t').RFLAGS = (cmpSpec ((Operand.mem (rsi.read t') : Operand n).read t')
      ((Operand.mem (rdi.read t') : Operand n).read t')).store t'.RFLAGS := rfl
  have hC : ((!((rcx.read (rcx.write (cmpsSpec n t') (rcx.read t' - 1))).setWidth 32 == 0#32)) &&&
      ((BitVec.extractLsb' (Int.toNat 6) (Int.toNat 1)
        (rcx.write (cmpsSpec n t') (rcx.read t' - 1)).RFLAGS == 1) == true)) =
      repeCmpsCont n t' := by
    have hb (r : BitVec 64) : (BitVec.extractLsb' 6 1 r == 1) = r.getLsbD 6 :=
      extractLsb'_one_beq r 6
    rw [rcx_read_write, setWidth32_beq_zero_of_lt (toNat_sub_one_lt_of_lt hcl' hc0),
      show (rcx.write (cmpsSpec n t') (rcx.read t' - 1)).RFLAGS =
        (cmpsSpec n t').RFLAGS from rfl,
      show Int.toNat 6 = 6 from rfl, show Int.toNat 1 = 1 from rfl, hb, hf]
    unfold repeCmpsCont
    rw [← StatusFlags.ofRFLAGS_store (cmpSpec _ _) t'.RFLAGS]
    show _ = (!(rcx.read t' - 1 == 0#64) && (StatusFlags.store _ t'.RFLAGS).getLsbD 6)
    cases (rcx.read t' - 1 == 0#64) <;> simp [HAnd.hAnd, AndOp.and, strictAnd]
  rw [hC]
  unfold repeCmpsSpec
  cases repeCmpsCont n t' <;> rfl

open scoped X86.Runtime.Syntax in
theorem compare_string_repeat_ne_a32 [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (hlock : ctx.lock_prefix_present = false) (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true) (hasz : ctx.asz_prefix_present = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : MemReadable t (rsi.read t) (n / 8)) (hdst : MemReadable t (rdi.read t) (n / 8))
    (hsl : (rsi.read t).toNat + n / 8 < 2^32) (hdl : (rdi.read t).toNat + n / 8 < 2^32)
    (hcl : (rcx.read t).toNat < 2^32) :
    (X86.Instructions.Compare_String ip ctx (n : Int) true false).run t =
      (.ok (), repneCmpsSpec n { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hop := compare_string_operation_a32 hcm
    { t with Next_IP := ip, Repeat_String_Operation := false }
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl
      rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) n hn ctx hseg hm64 hasz hds hes hdf (hsrc.of_external_eq rfl)
    (hdst.of_external_eq rfl) hsl hdl
  have haddr (u : RamState) :
      (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run u = (.ok 32, u) :=
    addressSize32_run ctx hm64 hasz u
  have hsub (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Subtract_int (n := 32) v 1) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 32)).run a = (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Is_Zero (size := 32) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#32), a) := rfl
  unfold X86.Instructions.Compare_String
  rw [assert_of_true (by rcases hn with rfl | rfl | rfl | rfl <;> decide), pure_bind]
  simp only [hlock, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false })) _
    (s := { t with Next_IP := ip }) rfl]
  refine (specM_bind_run _ _ (haddr _)).trans ?_
  simp (config := { decide := true }) only [assert_of_true, pure_bind]
  refine (specM_bind_run _ _ (rcxSlice32_run _)).trans ?_
  refine (specM_bind_run _ _ (hzero _ _)).trans ?_
  have hz : ((rcx.read { t with Next_IP := ip, Repeat_String_Operation := false }).setWidth 32 ==
      0#32) = false := by
    show ((rcx.read t).setWidth 32 == 0#32) = false
    rw [setWidth32_beq_zero_of_lt hcl]
    simpa using hcount
  rw [hz, ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
  rw [specM_bind_run _ _ (get_run _)]
  refine (specM_bind_run _ _ hop).trans ?_
  refine (specM_bind_run _ _ (rcxSlice32_run _)).trans ?_
  refine (specM_bind_run _ _ (hsub _ _)).trans ?_
  refine (specM_bind_run _ _ (writeRCX32_run _ _)).trans ?_
  refine (specM_bind_run _ _ (rcxSlice32_run _)).trans ?_
  refine (specM_bind_run _ _ (hzero _ _)).trans ?_
  refine (specM_bind_run _ _ (show (RFLAGS.ZF : X86.Runtime.SpecM X86.Exception RamState
    (BitVec 1)).run _ = (.ok _, _) from rfl)).trans ?_
  generalize ht' : { t with Next_IP := ip, Repeat_String_Operation := false } = t'
  have hcl' : (rcx.read t').toNat < 2^32 := by rw [← ht']; exact hcl
  have hc0 : rcx.read t' ≠ 0 := by rw [← ht']; exact hcount
  have hr : rcx.read (cmpsSpec n t') = rcx.read t' := by
    simp only [cmpsSpec]
    rw [Operand.read_write_reg_of_ne _ (by decide), Operand.read_write_reg_of_ne _ (by decide),
      Operand.read_setFlags, Operand.read_reg_dataAccess, Operand.read_reg_dataAccess]
  have hw : ((rcx.read (cmpsSpec n t')).setWidth 32 - 1).setWidth 64 = rcx.read t' - 1 := by
    rw [hr, setWidth64_sub_one_of_lt hcl' hc0]
  rw [hw]
  have hf : (cmpsSpec n t').RFLAGS = (cmpSpec ((Operand.mem (rsi.read t') : Operand n).read t')
      ((Operand.mem (rdi.read t') : Operand n).read t')).store t'.RFLAGS := rfl
  have hC : ((!((rcx.read (rcx.write (cmpsSpec n t') (rcx.read t' - 1))).setWidth 32 == 0#32)) &&&
      ((BitVec.extractLsb' (Int.toNat 6) (Int.toNat 1)
        (rcx.write (cmpsSpec n t') (rcx.read t' - 1)).RFLAGS == 1) == false)) =
      repneCmpsCont n t' := by
    have hb (r : BitVec 64) : (BitVec.extractLsb' 6 1 r == 1) = r.getLsbD 6 :=
      extractLsb'_one_beq r 6
    rw [rcx_read_write, setWidth32_beq_zero_of_lt (toNat_sub_one_lt_of_lt hcl' hc0),
      show (rcx.write (cmpsSpec n t') (rcx.read t' - 1)).RFLAGS =
        (cmpsSpec n t').RFLAGS from rfl,
      show Int.toNat 6 = 6 from rfl, show Int.toNat 1 = 1 from rfl, hb, hf]
    unfold repneCmpsCont
    rw [← StatusFlags.ofRFLAGS_store (cmpSpec _ _) t'.RFLAGS]
    show _ = (!(rcx.read t' - 1 == 0#64) && !(StatusFlags.store _ t'.RFLAGS).getLsbD 6)
    cases (rcx.read t' - 1 == 0#64) <;> simp [HAnd.hAnd, AndOp.and, strictAnd]
  rw [hC]
  unfold repneCmpsSpec
  cases repneCmpsCont n t' <;> rfl

theorem compare_string_repeat_zero_a32 [Bindings] (t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (hlock : ctx.lock_prefix_present = false) (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = true) (hcount : rcx.read t = 0) :
    (X86.Instructions.Compare_String ip ctx (n : Int) true true).run t =
      (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have haddr (u : RamState) :
      (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run u = (.ok 32, u) :=
    addressSize32_run ctx hm64 hasz u
  have hzero (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Is_Zero (size := 32) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#32), a) := rfl
  unfold X86.Instructions.Compare_String
  rw [assert_of_true (by rcases hn with rfl | rfl | rfl | rfl <;> decide), pure_bind]
  simp only [hlock, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false })) _
    (s := { t with Next_IP := ip }) rfl]
  refine (specM_bind_run _ _ (haddr _)).trans ?_
  simp (config := { decide := true }) only [assert_of_true, pure_bind]
  refine (specM_bind_run _ _ (rcxSlice32_run _)).trans ?_
  refine (specM_bind_run _ _ (hzero _ _)).trans ?_
  have hz : ((rcx.read { t with Next_IP := ip, Repeat_String_Operation := false }).setWidth 32 ==
      0#32) = true := by
    show ((rcx.read t).setWidth 32 == 0#32) = true
    rw [hcount]
    rfl
  rw [hz, ite_eq_left_of_eq_true _ _ (eq_true (by decide))]
  rfl

theorem compare_string_repeat_ne_zero_a32 [Bindings] (t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (hlock : ctx.lock_prefix_present = false) (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = true) (hcount : rcx.read t = 0) :
    (X86.Instructions.Compare_String ip ctx (n : Int) true false).run t =
      (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have haddr (u : RamState) :
      (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run u = (.ok 32, u) :=
    addressSize32_run ctx hm64 hasz u
  have hzero (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Is_Zero (size := 32) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#32), a) := rfl
  unfold X86.Instructions.Compare_String
  rw [assert_of_true (by rcases hn with rfl | rfl | rfl | rfl <;> decide), pure_bind]
  simp only [hlock, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false })) _
    (s := { t with Next_IP := ip }) rfl]
  refine (specM_bind_run _ _ (haddr _)).trans ?_
  simp (config := { decide := true }) only [assert_of_true, pure_bind]
  refine (specM_bind_run _ _ (rcxSlice32_run _)).trans ?_
  refine (specM_bind_run _ _ (hzero _ _)).trans ?_
  have hz : ((rcx.read { t with Next_IP := ip, Repeat_String_Operation := false }).setWidth 32 ==
      0#32) = true := by
    show ((rcx.read t).setWidth 32 == 0#32) = true
    rw [hcount]
    rfl
  rw [hz, ite_eq_left_of_eq_true _ _ (eq_true (by decide))]
  rfl

open scoped X86.Runtime.Syntax in
theorem compare_string_repeat_down [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (hlock : ctx.lock_prefix_present = false) (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true) (hasz : ctx.asz_prefix_present = false)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : MemReadable t (rsi.read t) (n / 8)) (hdst : MemReadable t (rdi.read t) (n / 8)) :
    (X86.Instructions.Compare_String ip ctx (n : Int) true true).run t =
      (.ok (), repeCmpsDownSpec n { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hop := compare_string_operation_down hcm
    { t with Next_IP := ip, Repeat_String_Operation := false }
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl
      rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) n hn ctx hseg hm64 hasz hds hes hdf (hsrc.of_external_eq rfl)
    (hdst.of_external_eq rfl)
  have haddr (u : RamState) :
      (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run u = (.ok 64, u) :=
    addressSize_run ctx hm64 hasz u
  have hsub (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Subtract_int (n := 64) v 1) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#64), a) := rfl
  unfold X86.Instructions.Compare_String
  rw [assert_of_true (by rcases hn with rfl | rfl | rfl | rfl <;> decide), pure_bind]
  simp only [hlock, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false })) _
    (s := { t with Next_IP := ip }) rfl]
  refine (specM_bind_run _ _ (haddr _)).trans ?_
  simp (config := { decide := true }) only [assert_of_true, pure_bind]
  refine (specM_bind_run _ _ (rcxSlice_run _)).trans ?_
  refine (specM_bind_run _ _ (hzero _ _)).trans ?_
  have hz :
      (rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } == 0#64) = false := by
    simpa using hcount
  rw [hz, ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
  rw [specM_bind_run _ _ (get_run _)]
  refine (specM_bind_run _ _ hop).trans ?_
  refine (specM_bind_run _ _ (rcxSlice_run _)).trans ?_
  refine (specM_bind_run _ _ (hsub _ _)).trans ?_
  refine (specM_bind_run _ _ (writeRCX64_run _ _)).trans ?_
  refine (specM_bind_run _ _ (rcxSlice_run _)).trans ?_
  refine (specM_bind_run _ _ (hzero _ _)).trans ?_
  refine (specM_bind_run _ _ (show (RFLAGS.ZF : X86.Runtime.SpecM X86.Exception RamState
    (BitVec 1)).run _ = (.ok _, _) from rfl)).trans ?_
  generalize ht' : { t with Next_IP := ip, Repeat_String_Operation := false } = t'
  have hr : rcx.read (cmpsDownSpec n t') = rcx.read t' := by
    simp only [cmpsDownSpec]
    rw [Operand.read_write_reg_of_ne _ (by decide), Operand.read_write_reg_of_ne _ (by decide),
      Operand.read_setFlags, Operand.read_reg_dataAccess, Operand.read_reg_dataAccess]
  have hf : (cmpsDownSpec n t').RFLAGS = (cmpSpec ((Operand.mem (rsi.read t') : Operand n).read t')
      ((Operand.mem (rdi.read t') : Operand n).read t')).store t'.RFLAGS := rfl
  have hC : ((!(rcx.read (rcx.write (cmpsDownSpec n t') (rcx.read (cmpsDownSpec n t') - 1)) ==
      0#64)) &&&
      ((BitVec.extractLsb' (Int.toNat 6) (Int.toNat 1)
        (rcx.write (cmpsDownSpec n t') (rcx.read (cmpsDownSpec n t') - 1)).RFLAGS == 1) == true)) =
      repeCmpsCont n t' := by
    have hb (r : BitVec 64) : (BitVec.extractLsb' 6 1 r == 1) = r.getLsbD 6 :=
      extractLsb'_one_beq r 6
    rw [rcx_read_write,
      show (rcx.write (cmpsDownSpec n t') (rcx.read (cmpsDownSpec n t') - 1)).RFLAGS =
        (cmpsDownSpec n t').RFLAGS from rfl,
      show Int.toNat 6 = 6 from rfl, show Int.toNat 1 = 1 from rfl, hb, hf, hr]
    unfold repeCmpsCont
    rw [← StatusFlags.ofRFLAGS_store (cmpSpec _ _) t'.RFLAGS]
    show _ = (!(rcx.read t' - 1 == 0#64) && (StatusFlags.store _ t'.RFLAGS).getLsbD 6)
    cases (rcx.read t' - 1 == 0#64) <;> simp [HAnd.hAnd, AndOp.and, strictAnd]
  rw [hC, hr]
  unfold repeCmpsDownSpec
  cases repeCmpsCont n t' <;> rfl

open scoped X86.Runtime.Syntax in
theorem compare_string_repeat_ne_down [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (hlock : ctx.lock_prefix_present = false) (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true) (hasz : ctx.asz_prefix_present = false)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : MemReadable t (rsi.read t) (n / 8)) (hdst : MemReadable t (rdi.read t) (n / 8)) :
    (X86.Instructions.Compare_String ip ctx (n : Int) true false).run t =
      (.ok (), repneCmpsDownSpec n { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hop := compare_string_operation_down hcm
    { t with Next_IP := ip, Repeat_String_Operation := false }
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl
      rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) n hn ctx hseg hm64 hasz hds hes hdf (hsrc.of_external_eq rfl)
    (hdst.of_external_eq rfl)
  have haddr (u : RamState) :
      (Address_Size ctx : X86.Runtime.SpecM X86.Exception RamState Int).run u = (.ok 64, u) :=
    addressSize_run ctx hm64 hasz u
  have hsub (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Subtract_int (n := 64) v 1) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#64), a) := rfl
  unfold X86.Instructions.Compare_String
  rw [assert_of_true (by rcases hn with rfl | rfl | rfl | rfl <;> decide), pure_bind]
  simp only [hlock, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false })) _
    (s := { t with Next_IP := ip }) rfl]
  refine (specM_bind_run _ _ (haddr _)).trans ?_
  simp (config := { decide := true }) only [assert_of_true, pure_bind]
  refine (specM_bind_run _ _ (rcxSlice_run _)).trans ?_
  refine (specM_bind_run _ _ (hzero _ _)).trans ?_
  have hz :
      (rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } == 0#64) = false := by
    simpa using hcount
  rw [hz, ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
  rw [specM_bind_run _ _ (get_run _)]
  refine (specM_bind_run _ _ hop).trans ?_
  refine (specM_bind_run _ _ (rcxSlice_run _)).trans ?_
  refine (specM_bind_run _ _ (hsub _ _)).trans ?_
  refine (specM_bind_run _ _ (writeRCX64_run _ _)).trans ?_
  refine (specM_bind_run _ _ (rcxSlice_run _)).trans ?_
  refine (specM_bind_run _ _ (hzero _ _)).trans ?_
  refine (specM_bind_run _ _ (show (RFLAGS.ZF : X86.Runtime.SpecM X86.Exception RamState
    (BitVec 1)).run _ = (.ok _, _) from rfl)).trans ?_
  generalize ht' : { t with Next_IP := ip, Repeat_String_Operation := false } = t'
  have hr : rcx.read (cmpsDownSpec n t') = rcx.read t' := by
    simp only [cmpsDownSpec]
    rw [Operand.read_write_reg_of_ne _ (by decide), Operand.read_write_reg_of_ne _ (by decide),
      Operand.read_setFlags, Operand.read_reg_dataAccess, Operand.read_reg_dataAccess]
  have hf : (cmpsDownSpec n t').RFLAGS = (cmpSpec ((Operand.mem (rsi.read t') : Operand n).read t')
      ((Operand.mem (rdi.read t') : Operand n).read t')).store t'.RFLAGS := rfl
  have hC : ((!(rcx.read (rcx.write (cmpsDownSpec n t') (rcx.read (cmpsDownSpec n t') - 1)) ==
      0#64)) &&&
      ((BitVec.extractLsb' (Int.toNat 6) (Int.toNat 1)
        (rcx.write (cmpsDownSpec n t') (rcx.read (cmpsDownSpec n t') - 1)).RFLAGS == 1) == false)) =
      repneCmpsCont n t' := by
    have hb (r : BitVec 64) : (BitVec.extractLsb' 6 1 r == 1) = r.getLsbD 6 :=
      extractLsb'_one_beq r 6
    rw [rcx_read_write,
      show (rcx.write (cmpsDownSpec n t') (rcx.read (cmpsDownSpec n t') - 1)).RFLAGS =
        (cmpsDownSpec n t').RFLAGS from rfl,
      show Int.toNat 6 = 6 from rfl, show Int.toNat 1 = 1 from rfl, hb, hf, hr]
    unfold repneCmpsCont
    rw [← StatusFlags.ofRFLAGS_store (cmpSpec _ _) t'.RFLAGS]
    show _ = (!(rcx.read t' - 1 == 0#64) && !(StatusFlags.store _ t'.RFLAGS).getLsbD 6)
    cases (rcx.read t' - 1 == 0#64) <;> simp [HAnd.hAnd, AndOp.and, strictAnd]
  rw [hC, hr]
  unfold repneCmpsDownSpec
  cases repneCmpsCont n t' <;> rfl

end X86Proofs
