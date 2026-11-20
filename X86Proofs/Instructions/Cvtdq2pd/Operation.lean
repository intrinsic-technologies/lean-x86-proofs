import X86Proofs.Core.Float

/-!
# CVTDQ2PD specification

`CVTDQ2PD xmm1, xmm2/m64` (`F3 0F E6 /r`) converts the two low signed doubleword integers of the
source to double precision: `DEST[64i+63:64i] ← Convert(SRC[32i+31:32i])` for `i` = 0, 1 (exact,
so no exception is raised in practice; lean-x86 still ORs each lane's flags into MXCSR). Each lane
and its flags are lean-x86's own `FP.From_Int` at that MXCSR (`fpFromInt`, `Core/Float.lean`);
there is no IEEE-754 library to state them against independently. The source is the 128-bit
register or the 64-bit memory operand (only its low 64 bits are read). `cvtdq2pdSpec mx a b` is
the result (the destination `a` is not read), `cvtdq2pdFlags mx a b` the exception flags,
`cvtdq2pdOk mx a b` that lean-x86 returns both lanes; lean-x86 computes them with
`Operations.CVTi2Pg 32 n 64 128`.
-/

namespace X86Proofs

open X86 X86.Helpers

/-- Lane `i` of the conversion and its flags. -/
def cvtdq2pdLane {n : Nat} (mx : BitVec 32) (b : BitVec n) (i : Nat) : BitVec 64 × BitVec 6 :=
  fpFromInt 32 64 mx (lane 32 b i)

/-- The two low doubleword lanes of `b` converted to double precision at MXCSR `mx`. -/
def cvtdq2pdSpec {n : Nat} (mx : BitVec 32) (_a : BitVec 128) (b : BitVec n) : BitVec 128 :=
  fpPacked 64 (cvtdq2pdLane mx b)

/-- The exception flags, both lanes' ORed. -/
def cvtdq2pdFlags {n : Nat} (mx : BitVec 32) (_a : BitVec 128) (b : BitVec n) : BitVec 6 :=
  fpPackedFlags 64 (cvtdq2pdLane mx b)

/-- lean-x86's conversion returns a value on both lanes (`FpFromIntOk`). -/
def cvtdq2pdOk {n : Nat} (mx : BitVec 32) (_a : BitVec 128) (b : BitVec n) : Prop :=
  ∀ i < 2, FpFromIntOk 32 64 mx (lane 32 b i)

theorem cvtdq2pd_operation [X86.Machine.Bindings] (n : Nat) (hn : n = 64 ∨ n = 128)
    (s : X86.Machine.RamState) (a : BitVec 128) (b : BitVec n) (ctx : Instruction_Context)
    (mod : BitVec 2) (hb : ctx.evex_b = 0) (hm : MxcsrPre s) (hok : cvtdq2pdOk s.MXCSR a b) :
    (X86.Instructions.Operations.CVTi2Pg 32 n 64 128 b ctx mod).run s =
      (.ok (cvtdq2pdSpec s.MXCSR a b),
        { s with MXCSR := mxOr s.MXCSR (cvtdq2pdFlags s.MXCSR a b) }) := by
  rcases hn with rfl | rfl <;> unfold X86.Instructions.Operations.CVTi2Pg <;>
    simp (config := { decide := true }) only [x86_runtime, hb, Int.reduceBEq, Bool.true_or,
      Bool.or_true, pure_bind] <;>
    refine (specM_bind_run _ _ (mxcsrMasks_run _)).trans ?_ <;>
    refine (specM_bind_run _ _ (mxcsrRC_run _)).trans ?_ <;>
    refine (specM_bind_run _ _ (liftM_run_of_ok (decodeRoundingMode_eq _) _)).trans ?_
  · fp_cvt_loop 2 32 64 64
      (fun i hi => fpFromInt_run 32 64 (.inl rfl) (.inr rfl) _ _ (hok i hi)) hm
  · fp_cvt_loop 2 32 128 64
      (fun i hi => fpFromInt_run 32 64 (.inl rfl) (.inr rfl) _ _ (hok i hi)) hm

end X86Proofs
