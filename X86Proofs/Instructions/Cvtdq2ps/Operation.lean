import X86Proofs.Core.Float

/-!
# CVTDQ2PS specification

`CVTDQ2PS xmm1, xmm2/m128` (`0F 5B /r`) converts the four signed doubleword integers of the source
to single precision: `DEST[32i+31:32i] ← Convert(SRC[32i+31:32i])` for `i` = 0 to 3, rounded as
MXCSR.RC says; the exception flags (precision only) of every lane are ORed into MXCSR. Each lane
and its flags are lean-x86's own `FP.From_Int` at that MXCSR (`fpFromInt`, `Core/Float.lean`);
there is no IEEE-754 library to state them against independently. `cvtdq2psSpec mx a b` is the
result (the destination `a` is not read), `cvtdq2psFlags mx a b` the exception flags,
`cvtdq2psOk mx a b` that lean-x86 returns every lane; lean-x86 computes them with
`Operations.CVTi2Pf 32 128 32 128`.

CVTPI2PD `xmm, mm` (`66 0F 2A`) converts the two doubleword lanes of an MMX register to double
precision with the same operation at other sizes: `cvtpi2pdSpec mx a b` (`fpPacked 64`),
`cvtpi2pdFlags`, `cvtpi2pdOk` (`Operations.CVTi2Pf 32 64 64 128`).
-/

namespace X86Proofs

open X86 X86.Helpers

/-- Lane `i` of the conversion and its flags. -/
def cvtdq2psLane (mx : BitVec 32) (b : BitVec 128) (i : Nat) : BitVec 32 × BitVec 6 :=
  fpFromInt 32 32 mx (lane 32 b i)

/-- The doubleword lanes of `b` converted to single precision at MXCSR `mx`. -/
def cvtdq2psSpec (mx : BitVec 32) (_a b : BitVec 128) : BitVec 128 :=
  fpPacked 32 (cvtdq2psLane mx b)

/-- The exception flags, every lane's ORed. -/
def cvtdq2psFlags (mx : BitVec 32) (_a b : BitVec 128) : BitVec 6 :=
  fpPackedFlags 32 (cvtdq2psLane mx b)

/-- lean-x86's conversion returns a value on every lane (`FpFromIntOk`). -/
def cvtdq2psOk (mx : BitVec 32) (_a b : BitVec 128) : Prop :=
  ∀ i < 4, FpFromIntOk 32 32 mx (lane 32 b i)

/-- Lane `i` of the conversion and its flags. -/
def cvtpi2pdLane (mx : BitVec 32) (b : BitVec 64) (i : Nat) : BitVec 64 × BitVec 6 :=
  fpFromInt 32 64 mx (lane 32 b i)

/-- The two doubleword lanes of `b` converted to double precision at MXCSR `mx`. -/
def cvtpi2pdSpec (mx : BitVec 32) (_a : BitVec 128) (b : BitVec 64) : BitVec 128 :=
  fpPacked 64 (cvtpi2pdLane mx b)

/-- The exception flags, both lanes' ORed. -/
def cvtpi2pdFlags (mx : BitVec 32) (_a : BitVec 128) (b : BitVec 64) : BitVec 6 :=
  fpPackedFlags 64 (cvtpi2pdLane mx b)

/-- lean-x86's conversion returns a value on both lanes (`FpFromIntOk`). -/
def cvtpi2pdOk (mx : BitVec 32) (_a : BitVec 128) (b : BitVec 64) : Prop :=
  ∀ i < 2, FpFromIntOk 32 64 mx (lane 32 b i)

theorem cvtdq2ps_operation [X86.Machine.Bindings] (s : X86.Machine.RamState) (a b : BitVec 128)
    (ctx : Instruction_Context) (mod : BitVec 2) (hb : ctx.evex_b = 0) (hm : MxcsrPre s)
    (hok : cvtdq2psOk s.MXCSR a b) :
    (X86.Instructions.Operations.CVTi2Pf 32 128 32 128 b ctx mod).run s =
      (.ok (cvtdq2psSpec s.MXCSR a b),
        { s with MXCSR := mxOr s.MXCSR (cvtdq2psFlags s.MXCSR a b) }) := by
  unfold X86.Instructions.Operations.CVTi2Pf
  simp (config := { decide := true }) only [x86_runtime, hb, Int.reduceBEq, Bool.true_or,
    Bool.or_true, pure_bind]
  refine (specM_bind_run _ _ (mxcsrMasks_run _)).trans ?_
  refine (specM_bind_run _ _ (mxcsrRC_run _)).trans ?_
  refine (specM_bind_run _ _ (liftM_run_of_ok (decodeRoundingMode_eq _) _)).trans ?_
  fp_cvt_loop 4 32 128 32 (fun i hi => fpFromInt_run 32 32 (.inl rfl) (.inl rfl) _ _ (hok i hi)) hm

theorem cvtpi2pd_operation [X86.Machine.Bindings] (s : X86.Machine.RamState) (a : BitVec 128)
    (b : BitVec 64) (ctx : Instruction_Context) (mod : BitVec 2) (hb : ctx.evex_b = 0)
    (hm : MxcsrPre s) (hok : cvtpi2pdOk s.MXCSR a b) :
    (X86.Instructions.Operations.CVTi2Pf 32 64 64 128 b ctx mod).run s =
      (.ok (cvtpi2pdSpec s.MXCSR a b),
        { s with MXCSR := mxOr s.MXCSR (cvtpi2pdFlags s.MXCSR a b) }) := by
  unfold X86.Instructions.Operations.CVTi2Pf
  simp (config := { decide := true }) only [x86_runtime, hb, Int.reduceBEq, Bool.true_or,
    Bool.or_true, pure_bind]
  refine (specM_bind_run _ _ (mxcsrMasks_run _)).trans ?_
  refine (specM_bind_run _ _ (mxcsrRC_run _)).trans ?_
  refine (specM_bind_run _ _ (liftM_run_of_ok (decodeRoundingMode_eq _) _)).trans ?_
  fp_cvt_loop 2 32 64 64 (fun i hi => fpFromInt_run 32 64 (.inl rfl) (.inr rfl) _ _ (hok i hi)) hm

end X86Proofs
