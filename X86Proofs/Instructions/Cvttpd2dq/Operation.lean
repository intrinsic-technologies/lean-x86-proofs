import X86Proofs.Core.Float

/-!
# CVTTPD2DQ specification

`CVTTPD2DQ xmm1, xmm2/m128` (`66 0F E6 /r`) converts the two double-precision elements of the
source to signed doubleword integers, truncating:
`DEST[32i+31:32i] ← Convert_To_Integer_Truncate(SRC[64i+63:64i])` for `i` = 0, 1, `DEST[127:64]`
zero, with MXCSR's DAZ; a NaN or an out-of-range value gives `80000000H` and the invalid flag. The
exception flags of both lanes, as `FP.Prioritize_Operand_Exceptions` keeps them with every
exception masked (`fpOperandPrio`), are ORed into MXCSR. Each lane is lean-x86's own `FP.To_Int`
(`fpToInt`, `Core/Float.lean`). `cvttpd2dqSpec mx a b` is the result (the destination `a` is not
read), `cvttpd2dqFlags mx a b` the exception flags, `cvttpd2dqOk mx a b` that lean-x86 returns
both lanes; lean-x86 computes them with `Operations.CVTTPg2i 64 128 32 128`, which may diverge.

The MMX forms CVTTPD2PI `mm, xmm/m128` (`66 0F 2C`) truncate both lanes into an MMX register:
`cvttpd2piSpec mx b`, `cvttpd2piFlags`, `cvttpd2piOk` (`Operations.CVTTPg2i 64 128 32 64`;
`fpLanesOnto`).
-/

namespace X86Proofs

open X86 X86.Helpers

/-- Lane `i` of the conversion and its flags (toward zero). -/
def cvttpd2dqLane (mx : BitVec 32) (b : BitVec 128) (i : Nat) : BitVec 32 × BitVec 6 :=
  ((fpToInt 64 32 .Rounding_Mode_RTZ mx (lane 64 b i)).1,
    fpOperandPrio (fpToInt 64 32 .Rounding_Mode_RTZ mx (lane 64 b i)).2)

/-- The two double-precision lanes of `b` truncated to doubleword integers (DAZ from `mx`), in
the two low lanes of zero. -/
def cvttpd2dqSpec (mx : BitVec 32) (_a b : BitVec 128) : BitVec 128 :=
  fpLanes 2 32 (cvttpd2dqLane mx b)

/-- The exception flags, both lanes' ORed. -/
def cvttpd2dqFlags (mx : BitVec 32) (_a b : BitVec 128) : BitVec 6 :=
  fpLanesFlags 2 32 (cvttpd2dqLane mx b)

/-- lean-x86's conversion returns a value on both lanes (`FpToIntOk`). -/
def cvttpd2dqOk (mx : BitVec 32) (_a b : BitVec 128) : Prop :=
  ∀ i < 2, FpToIntOk 64 32 .Rounding_Mode_RTZ mx (lane 64 b i)

/-- Lane `i` of the conversion and its flags (toward zero). -/
def cvttpd2piLane (mx : BitVec 32) (b : BitVec 128) (i : Nat) : BitVec 32 × BitVec 6 :=
  ((fpToInt 64 32 .Rounding_Mode_RTZ mx (lane 64 b i)).1,
    fpOperandPrio (fpToInt 64 32 .Rounding_Mode_RTZ mx (lane 64 b i)).2)

/-- The two double-precision lanes of `b` truncated to doubleword integers. -/
def cvttpd2piSpec (mx : BitVec 32) (b : BitVec 128) : BitVec 64 :=
  (fpLanesOnto 2 32 (cvttpd2piLane mx b) (0 : BitVec 64)).2

/-- The exception flags, both lanes' ORed. -/
def cvttpd2piFlags (mx : BitVec 32) (b : BitVec 128) : BitVec 6 :=
  (fpLanesOnto 2 32 (cvttpd2piLane mx b) (0 : BitVec 64)).1

/-- lean-x86's conversion returns a value on both lanes (`FpToIntOk`). -/
def cvttpd2piOk (mx : BitVec 32) (b : BitVec 128) : Prop :=
  ∀ i < 2, FpToIntOk 64 32 .Rounding_Mode_RTZ mx (lane 64 b i)

theorem cvttpd2dq_operation [X86.Machine.Bindings] (s : X86.Machine.RamState) (a b : BitVec 128)
    (hm : MxcsrPre s) (hok : cvttpd2dqOk s.MXCSR a b) :
    (X86.Instructions.Operations.CVTTPg2i 64 128 32 128 b).run s =
      some (.ok (cvttpd2dqSpec s.MXCSR a b),
        { s with MXCSR := mxOr s.MXCSR (cvttpd2dqFlags s.MXCSR a b) }) := by
  unfold X86.Instructions.Operations.CVTTPg2i
  simp (config := { decide := true }) only [x86_runtime, Int.reduceBEq, Bool.or_true, pure_bind]
  refine (partialSpecM_liftTotal_bind_run _ _ (getDAZ_run _ (by decide) _)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (mxcsrMasks_run _)).trans ?_
  fp_cvt_loop_partial 2 64 128 32 (fun i hi => fpToInt_run 64 32 _ _ _ (hok i hi)) hm masked

theorem cvttpd2pi_operation [X86.Machine.Bindings] (s : X86.Machine.RamState) (b : BitVec 128)
    (hm : MxcsrPre s) (hok : cvttpd2piOk s.MXCSR b) :
    (X86.Instructions.Operations.CVTTPg2i 64 128 32 64 b).run s =
      some (.ok (cvttpd2piSpec s.MXCSR b),
        { s with MXCSR := mxOr s.MXCSR (cvttpd2piFlags s.MXCSR b) }) := by
  unfold X86.Instructions.Operations.CVTTPg2i
  simp (config := { decide := true }) only [x86_runtime, Int.reduceBEq, pure_bind]
  refine (partialSpecM_liftTotal_bind_run _ _ (getDAZ_run _ (by decide) _)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (mxcsrMasks_run _)).trans ?_
  fp_cvt_loop_partial 2 64 128 32 (fun i hi => fpToInt_run 64 32 _ _ _ (hok i hi)) hm masked
    into 64

end X86Proofs
