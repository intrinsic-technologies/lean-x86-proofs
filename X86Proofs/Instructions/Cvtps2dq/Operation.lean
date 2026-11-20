import X86Proofs.Core.Float

/-!
# CVTPS2DQ specification

`CVTPS2DQ xmm1, xmm2/m128` (`66 0F 5B /r`) converts the four single-precision elements of the
source to signed doubleword integers: `DEST[32i+31:32i] ← Convert_To_Integer(SRC[32i+31:32i])`
for `i` = 0 to 3, rounded as MXCSR.RC says, with MXCSR's DAZ; a NaN or an out-of-range value
gives the integer indefinite value `80000000H` and the invalid flag. The exception flags of every
lane are ORed into MXCSR. Each lane and its flags are lean-x86's own `FP.To_Int` (`fpToInt`,
`Core/Float.lean`); there is no IEEE-754 library to state them against independently.
`cvtps2dqSpec mx a b` is the result (the destination `a` is not read), `cvtps2dqFlags mx a b`
the exception flags, `cvtps2dqOk mx a b` that lean-x86 returns every lane; lean-x86 computes them
with `Operations.CVTPf2i 32 128 32 128`, which may diverge (`PartialSpecM`).

The MMX forms CVTPS2PI `mm, xmm/m64` (`NP 0F 2D`) convert the two low lanes into an MMX register:
`cvtps2piSpec mx b`, `cvtps2piFlags`, `cvtps2piOk` (`Operations.CVTPf2i 32 n 32 64`, `n` = 128 for
an XMM source, 64 for `m64`; `fpLanesOnto`).
-/

namespace X86Proofs

open X86 X86.Helpers

/-- Lane `i` of the conversion and its flags (MXCSR's rounding control). -/
def cvtps2dqLane (mx : BitVec 32) (b : BitVec 128) (i : Nat) : BitVec 32 × BitVec 6 :=
  fpToInt 32 32 (rcMode (mxRc mx)) mx (lane 32 b i)

/-- The single-precision lanes of `b` converted to doubleword integers at MXCSR `mx`. -/
def cvtps2dqSpec (mx : BitVec 32) (_a b : BitVec 128) : BitVec 128 :=
  fpPacked 32 (cvtps2dqLane mx b)

/-- The exception flags, every lane's ORed. -/
def cvtps2dqFlags (mx : BitVec 32) (_a b : BitVec 128) : BitVec 6 :=
  fpPackedFlags 32 (cvtps2dqLane mx b)

/-- lean-x86's conversion returns a value on every lane (`FpToIntOk`). -/
def cvtps2dqOk (mx : BitVec 32) (_a b : BitVec 128) : Prop :=
  ∀ i < 4, FpToIntOk 32 32 (rcMode (mxRc mx)) mx (lane 32 b i)

/-- Lane `i` of the conversion and its flags (MXCSR's rounding control). -/
def cvtps2piLane {n : Nat} (mx : BitVec 32) (b : BitVec n) (i : Nat) : BitVec 32 × BitVec 6 :=
  fpToInt 32 32 (rcMode (mxRc mx)) mx (lane 32 b i)

/-- The two low single-precision lanes of `b` converted to doubleword integers at MXCSR `mx`. -/
def cvtps2piSpec {n : Nat} (mx : BitVec 32) (b : BitVec n) : BitVec 64 :=
  (fpLanesOnto 2 32 (cvtps2piLane mx b) (0 : BitVec 64)).2

/-- The exception flags, both lanes' ORed. -/
def cvtps2piFlags {n : Nat} (mx : BitVec 32) (b : BitVec n) : BitVec 6 :=
  (fpLanesOnto 2 32 (cvtps2piLane mx b) (0 : BitVec 64)).1

/-- lean-x86's conversion returns a value on both lanes (`FpToIntOk`). -/
def cvtps2piOk {n : Nat} (mx : BitVec 32) (b : BitVec n) : Prop :=
  ∀ i < 2, FpToIntOk 32 32 (rcMode (mxRc mx)) mx (lane 32 b i)

theorem cvtps2dq_operation [X86.Machine.Bindings] (s : X86.Machine.RamState) (a b : BitVec 128)
    (ctx : Instruction_Context) (mod : BitVec 2) (hb : ctx.evex_b = 0) (hm : MxcsrPre s)
    (hok : cvtps2dqOk s.MXCSR a b) :
    (X86.Instructions.Operations.CVTPf2i 32 128 32 128 b ctx mod).run s =
      some (.ok (cvtps2dqSpec s.MXCSR a b),
        { s with MXCSR := mxOr s.MXCSR (cvtps2dqFlags s.MXCSR a b) }) := by
  unfold X86.Instructions.Operations.CVTPf2i
  simp (config := { decide := true }) only [x86_runtime, hb, pure_bind, BitVec.reduceBEq]
  refine (partialSpecM_liftTotal_bind_run _ _ (getDAZ_run _ (by decide) _)).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ (mxcsrMasks_run _)).trans ?_
  simp only [and_false_left, Bool.false_eq_true, ↓reduceIte]
  refine (partialSpecM_liftTotal_bind_run _ _ (mxcsrRC_run _)).trans ?_
  refine (partialSpecM_bind_run _ _
    (partialSpecM_liftM_run_of_ok (decodeRoundingMode_eq _) _)).trans ?_
  fp_cvt_loop_partial 4 32 128 32 (fun i hi => fpToInt_run 32 32 _ _ _ (hok i hi)) hm

theorem cvtps2pi_operation [X86.Machine.Bindings] (n : Nat) (hn : n = 64 ∨ n = 128)
    (s : X86.Machine.RamState) (b : BitVec n) (ctx : Instruction_Context) (mod : BitVec 2)
    (hb : ctx.evex_b = 0) (hm : MxcsrPre s) (hok : cvtps2piOk s.MXCSR b) :
    (X86.Instructions.Operations.CVTPf2i 32 n 32 64 b ctx mod).run s =
      some (.ok (cvtps2piSpec s.MXCSR b),
        { s with MXCSR := mxOr s.MXCSR (cvtps2piFlags s.MXCSR b) }) := by
  rcases hn with rfl | rfl <;> unfold X86.Instructions.Operations.CVTPf2i <;>
    simp (config := { decide := true }) only [x86_runtime, hb, pure_bind, BitVec.reduceBEq] <;>
    refine (partialSpecM_liftTotal_bind_run _ _ (getDAZ_run _ (by decide) _)).trans ?_ <;>
    refine (partialSpecM_liftTotal_bind_run _ _ (mxcsrMasks_run _)).trans ?_ <;>
    simp only [and_false_left, Bool.false_eq_true, ↓reduceIte] <;>
    refine (partialSpecM_liftTotal_bind_run _ _ (mxcsrRC_run _)).trans ?_ <;>
    refine (partialSpecM_bind_run _ _
      (partialSpecM_liftM_run_of_ok (decodeRoundingMode_eq _) _)).trans ?_
  · fp_cvt_loop_partial 2 32 64 32 (fun i hi => fpToInt_run 32 32 _ _ _ (hok i hi)) hm into 64
  · fp_cvt_loop_partial 2 32 128 32 (fun i hi => fpToInt_run 32 32 _ _ _ (hok i hi)) hm into 64

end X86Proofs
