import X86Proofs.Core.Float

/-!
# CVTTPS2DQ specification

`CVTTPS2DQ xmm1, xmm2/m128` (`F3 0F 5B /r`) converts the four single-precision elements of the
source to signed doubleword integers, truncating (rounding toward zero whatever MXCSR.RC says):
`DEST[32i+31:32i] ← Convert_To_Integer_Truncate(SRC[32i+31:32i])` for `i` = 0 to 3, with MXCSR's
DAZ; a NaN or an out-of-range value gives `80000000H` and the invalid flag. The exception flags of
every lane, with every exception masked as `FP.Prioritize_Operand_Exceptions` keeps them
(`fpOperandPrio`), are ORed into MXCSR. Each lane is lean-x86's own `FP.To_Int` (`fpToInt`,
`Core/Float.lean`). `cvttps2dqSpec mx a b` is the result (the destination `a` is not read),
`cvttps2dqFlags mx a b` the exception flags, `cvttps2dqOk mx a b` that lean-x86 returns every
lane; lean-x86 computes them with `Operations.CVTTPf2i 32 128 32 128`, which may diverge.

The MMX forms CVTTPS2PI `mm, xmm/m64` (`NP 0F 2C`) truncate the two low lanes into an MMX register:
`cvttps2piSpec mx b`, `cvttps2piFlags`, `cvttps2piOk` (`Operations.CVTTPf2i 32 n 32 64`;
`fpLanesOnto`).
-/

namespace X86Proofs

open X86 X86.Helpers

/-- Lane `i` of the conversion and its flags (toward zero). -/
def cvttps2dqLane (mx : BitVec 32) (b : BitVec 128) (i : Nat) : BitVec 32 × BitVec 6 :=
  ((fpToInt 32 32 .Rounding_Mode_RTZ mx (lane 32 b i)).1,
    fpOperandPrio (fpToInt 32 32 .Rounding_Mode_RTZ mx (lane 32 b i)).2)

/-- The single-precision lanes of `b` truncated to doubleword integers (DAZ from `mx`). -/
def cvttps2dqSpec (mx : BitVec 32) (_a b : BitVec 128) : BitVec 128 :=
  fpPacked 32 (cvttps2dqLane mx b)

/-- The exception flags, every lane's ORed. -/
def cvttps2dqFlags (mx : BitVec 32) (_a b : BitVec 128) : BitVec 6 :=
  fpPackedFlags 32 (cvttps2dqLane mx b)

/-- lean-x86's conversion returns a value on every lane (`FpToIntOk`). -/
def cvttps2dqOk (mx : BitVec 32) (_a b : BitVec 128) : Prop :=
  ∀ i < 4, FpToIntOk 32 32 .Rounding_Mode_RTZ mx (lane 32 b i)

/-- Lane `i` of the conversion and its flags (toward zero). -/
def cvttps2piLane {n : Nat} (mx : BitVec 32) (b : BitVec n) (i : Nat) : BitVec 32 × BitVec 6 :=
  ((fpToInt 32 32 .Rounding_Mode_RTZ mx (lane 32 b i)).1,
    fpOperandPrio (fpToInt 32 32 .Rounding_Mode_RTZ mx (lane 32 b i)).2)

/-- The two low single-precision lanes of `b` truncated to doubleword integers. -/
def cvttps2piSpec {n : Nat} (mx : BitVec 32) (b : BitVec n) : BitVec 64 :=
  (fpLanesOnto 2 32 (cvttps2piLane mx b) (0 : BitVec 64)).2

/-- The exception flags, both lanes' ORed. -/
def cvttps2piFlags {n : Nat} (mx : BitVec 32) (b : BitVec n) : BitVec 6 :=
  (fpLanesOnto 2 32 (cvttps2piLane mx b) (0 : BitVec 64)).1

/-- lean-x86's conversion returns a value on both lanes (`FpToIntOk`). -/
def cvttps2piOk {n : Nat} (mx : BitVec 32) (b : BitVec n) : Prop :=
  ∀ i < 2, FpToIntOk 32 32 .Rounding_Mode_RTZ mx (lane 32 b i)

theorem cvttps2dq_operation [X86.Machine.Bindings] (s : X86.Machine.RamState) (a b : BitVec 128)
    (hm : MxcsrPre s) (hok : cvttps2dqOk s.MXCSR a b) :
    (X86.Instructions.Operations.CVTTPf2i 32 128 32 128 b).run s =
      some (.ok (cvttps2dqSpec s.MXCSR a b),
        { s with MXCSR := mxOr s.MXCSR (cvttps2dqFlags s.MXCSR a b) }) := by
  unfold X86.Instructions.Operations.CVTTPf2i
  simp (config := { decide := true }) only [x86_runtime, pure_bind]
  refine (partialSpecM_liftTotal_bind_run _ _ (getDAZ_run _ (by decide) _)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (mxcsrMasks_run _)).trans ?_
  fp_cvt_loop_partial 4 32 128 32 (fun i hi => fpToInt_run 32 32 _ _ _ (hok i hi)) hm masked

theorem cvttps2pi_operation [X86.Machine.Bindings] (n : Nat) (hn : n = 64 ∨ n = 128)
    (s : X86.Machine.RamState) (b : BitVec n) (hm : MxcsrPre s) (hok : cvttps2piOk s.MXCSR b) :
    (X86.Instructions.Operations.CVTTPf2i 32 n 32 64 b).run s =
      some (.ok (cvttps2piSpec s.MXCSR b),
        { s with MXCSR := mxOr s.MXCSR (cvttps2piFlags s.MXCSR b) }) := by
  rcases hn with rfl | rfl <;> unfold X86.Instructions.Operations.CVTTPf2i <;>
    simp (config := { decide := true }) only [x86_runtime, pure_bind] <;>
    refine (partialSpecM_liftTotal_bind_run _ _ (getDAZ_run _ (by decide) _)).trans ?_ <;>
    refine (partialSpecM_liftTotal_bind_run _ _ (mxcsrMasks_run _)).trans ?_
  · fp_cvt_loop_partial 2 32 64 32 (fun i hi => fpToInt_run 32 32 _ _ _ (hok i hi)) hm masked
      into 64
  · fp_cvt_loop_partial 2 32 128 32 (fun i hi => fpToInt_run 32 32 _ _ _ (hok i hi)) hm masked
      into 64

end X86Proofs
