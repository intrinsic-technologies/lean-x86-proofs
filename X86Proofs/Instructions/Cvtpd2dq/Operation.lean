import X86Proofs.Core.Float

/-!
# CVTPD2DQ specification

`CVTPD2DQ xmm1, xmm2/m128` (`F2 0F E6 /r`) converts the two double-precision elements of the
source to signed doubleword integers: `DEST[32i+31:32i] ← Convert_To_Integer(SRC[64i+63:64i])`
for `i` = 0, 1, `DEST[127:64]` zero, rounded as MXCSR.RC says, with MXCSR's DAZ; a NaN or an
out-of-range value gives `80000000H` and the invalid flag. The exception flags of both lanes are
ORed into MXCSR. Each lane is lean-x86's own `FP.To_Int` (`fpToInt`, `Core/Float.lean`).
`cvtpd2dqSpec mx a b` is the result (the destination `a` is not read), `cvtpd2dqFlags mx a b` the
exception flags, `cvtpd2dqOk mx a b` that lean-x86 returns both lanes; lean-x86 computes them with
`Operations.CVTPg2i 64 128 32 128`, which may diverge.

The MMX forms CVTPD2PI `mm, xmm/m128` (`66 0F 2D`) convert both lanes into an MMX register:
`cvtpd2piSpec mx b`, `cvtpd2piFlags`, `cvtpd2piOk` (`Operations.CVTPg2i 64 128 32 64`;
`fpLanesOnto`).
-/

namespace X86Proofs

open X86 X86.Helpers

/-- Lane `i` of the conversion and its flags (MXCSR's rounding control). -/
def cvtpd2dqLane (mx : BitVec 32) (b : BitVec 128) (i : Nat) : BitVec 32 × BitVec 6 :=
  fpToInt 64 32 (rcMode (mxRc mx)) mx (lane 64 b i)

/-- The two double-precision lanes of `b` converted to doubleword integers at MXCSR `mx`, in the
two low lanes of zero. -/
def cvtpd2dqSpec (mx : BitVec 32) (_a b : BitVec 128) : BitVec 128 :=
  fpLanes 2 32 (cvtpd2dqLane mx b)

/-- The exception flags, both lanes' ORed. -/
def cvtpd2dqFlags (mx : BitVec 32) (_a b : BitVec 128) : BitVec 6 :=
  fpLanesFlags 2 32 (cvtpd2dqLane mx b)

/-- lean-x86's conversion returns a value on both lanes (`FpToIntOk`). -/
def cvtpd2dqOk (mx : BitVec 32) (_a b : BitVec 128) : Prop :=
  ∀ i < 2, FpToIntOk 64 32 (rcMode (mxRc mx)) mx (lane 64 b i)

/-- Lane `i` of the conversion and its flags (MXCSR's rounding control). -/
def cvtpd2piLane (mx : BitVec 32) (b : BitVec 128) (i : Nat) : BitVec 32 × BitVec 6 :=
  fpToInt 64 32 (rcMode (mxRc mx)) mx (lane 64 b i)

/-- The two double-precision lanes of `b` converted to doubleword integers at MXCSR `mx`. -/
def cvtpd2piSpec (mx : BitVec 32) (b : BitVec 128) : BitVec 64 :=
  (fpLanesOnto 2 32 (cvtpd2piLane mx b) (0 : BitVec 64)).2

/-- The exception flags, both lanes' ORed. -/
def cvtpd2piFlags (mx : BitVec 32) (b : BitVec 128) : BitVec 6 :=
  (fpLanesOnto 2 32 (cvtpd2piLane mx b) (0 : BitVec 64)).1

/-- lean-x86's conversion returns a value on both lanes (`FpToIntOk`). -/
def cvtpd2piOk (mx : BitVec 32) (b : BitVec 128) : Prop :=
  ∀ i < 2, FpToIntOk 64 32 (rcMode (mxRc mx)) mx (lane 64 b i)

theorem cvtpd2dq_operation [X86.Machine.Bindings] (s : X86.Machine.RamState) (a b : BitVec 128)
    (ctx : Instruction_Context) (mod : BitVec 2) (hb : ctx.evex_b = 0) (hm : MxcsrPre s)
    (hok : cvtpd2dqOk s.MXCSR a b) :
    (X86.Instructions.Operations.CVTPg2i 64 128 32 128 b ctx mod).run s =
      some (.ok (cvtpd2dqSpec s.MXCSR a b),
        { s with MXCSR := mxOr s.MXCSR (cvtpd2dqFlags s.MXCSR a b) }) := by
  unfold X86.Instructions.Operations.CVTPg2i
  simp (config := { decide := true }) only [x86_runtime, hb, pure_bind, BitVec.reduceBEq]
  refine (partialSpecM_liftTotal_bind_run _ _ (getDAZ_run _ (by decide) _)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (mxcsrMasks_run _)).trans ?_
  simp only [and_false_left, Bool.false_eq_true, ↓reduceIte]
  refine (partialSpecM_liftTotal_bind_run _ _ (mxcsrRC_run _)).trans ?_
  refine (partialSpecM_bind_run _ _
    (partialSpecM_liftM_run_of_ok (decodeRoundingMode_eq _) _)).trans ?_
  fp_cvt_loop_partial 2 64 128 32 (fun i hi => fpToInt_run 64 32 _ _ _ (hok i hi)) hm

theorem cvtpd2pi_operation [X86.Machine.Bindings] (s : X86.Machine.RamState) (b : BitVec 128)
    (ctx : Instruction_Context) (mod : BitVec 2) (hb : ctx.evex_b = 0) (hm : MxcsrPre s)
    (hok : cvtpd2piOk s.MXCSR b) :
    (X86.Instructions.Operations.CVTPg2i 64 128 32 64 b ctx mod).run s =
      some (.ok (cvtpd2piSpec s.MXCSR b),
        { s with MXCSR := mxOr s.MXCSR (cvtpd2piFlags s.MXCSR b) }) := by
  unfold X86.Instructions.Operations.CVTPg2i
  simp (config := { decide := true }) only [x86_runtime, hb, pure_bind, BitVec.reduceBEq]
  refine (partialSpecM_liftTotal_bind_run _ _ (getDAZ_run _ (by decide) _)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (mxcsrMasks_run _)).trans ?_
  simp only [and_false_left, Bool.false_eq_true, ↓reduceIte]
  refine (partialSpecM_liftTotal_bind_run _ _ (mxcsrRC_run _)).trans ?_
  refine (partialSpecM_bind_run _ _
    (partialSpecM_liftM_run_of_ok (decodeRoundingMode_eq _) _)).trans ?_
  fp_cvt_loop_partial 2 64 128 32 (fun i hi => fpToInt_run 64 32 _ _ _ (hok i hi)) hm into 64

end X86Proofs
