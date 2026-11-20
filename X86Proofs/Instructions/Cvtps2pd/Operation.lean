import X86Proofs.Core.Float

/-!
# CVTPS2PD specification

`CVTPS2PD xmm1, xmm2/m64` (`0F 5A /r`) converts the two low single-precision elements of the
source to double precision: `DEST[64i+63:64i] ← Convert(SRC[32i+31:32i])` for `i` = 0, 1, with
MXCSR's DAZ (the conversion is exact; lean-x86 flushes a tiny result to zero); the exception flags
of each lane (as `FP.Prioritize_Operand_Exceptions` reports them) are ORed into MXCSR. Each lane
and its flags are lean-x86's own `FP.Convert` at that MXCSR (`fpConvert`, `Core/Float.lean`);
there is no IEEE-754 library to state them against independently. The source is the 128-bit
register or the 64-bit memory operand (only its low 64 bits are read). `cvtps2pdSpec mx a b` is
the result (the destination `a` is not read), `cvtps2pdFlags mx a b` the exception flags,
`cvtps2pdOk mx a b` that lean-x86 returns both lanes; lean-x86 computes them with
`Operations.CVTPf2Pg 32 n 64 128`.
-/

namespace X86Proofs

open X86 X86.Helpers

/-- Lane `i` of the conversion and its flags. -/
def cvtps2pdLane {n : Nat} (mx : BitVec 32) (b : BitVec n) (i : Nat) : BitVec 64 × BitVec 6 :=
  ((fpConvert 32 64 .Rounding_Mode_RNE true mx (lane 32 b i)).1,
    fpOperandPrio (fpConvert 32 64 .Rounding_Mode_RNE true mx (lane 32 b i)).2)

/-- The two low single-precision lanes of `b` converted to double precision at MXCSR `mx`. -/
def cvtps2pdSpec {n : Nat} (mx : BitVec 32) (_a : BitVec 128) (b : BitVec n) : BitVec 128 :=
  fpPacked 64 (cvtps2pdLane mx b)

/-- The exception flags, both lanes' ORed. -/
def cvtps2pdFlags {n : Nat} (mx : BitVec 32) (_a : BitVec 128) (b : BitVec n) : BitVec 6 :=
  fpPackedFlags 64 (cvtps2pdLane mx b)

/-- lean-x86's conversion returns a value on both lanes (`FpConvertOk`). -/
def cvtps2pdOk {n : Nat} (mx : BitVec 32) (_a : BitVec 128) (b : BitVec n) : Prop :=
  ∀ i < 2, FpConvertOk 32 64 .Rounding_Mode_RNE true mx (lane 32 b i)

theorem cvtps2pd_operation [X86.Machine.Bindings] (n : Nat) (hn : n = 64 ∨ n = 128)
    (s : X86.Machine.RamState) (a : BitVec 128) (b : BitVec n) (hm : MxcsrPre s)
    (hok : cvtps2pdOk s.MXCSR a b) :
    (X86.Instructions.Operations.CVTPf2Pg 32 n 64 128 b).run s =
      (.ok (cvtps2pdSpec s.MXCSR a b),
        { s with MXCSR := mxOr s.MXCSR (cvtps2pdFlags s.MXCSR a b) }) := by
  rcases hn with rfl | rfl <;> unfold X86.Instructions.Operations.CVTPf2Pg <;>
    simp (config := { decide := true }) only [x86_runtime, Int.reduceBEq, Bool.true_or,
      Bool.or_true, pure_bind] <;>
    refine (specM_bind_run _ _ (getDAZ_run _ (by decide) _)).trans ?_ <;>
    refine (specM_bind_run _ _ (mxcsrMasks_run _)).trans ?_
  · fp_cvt_loop 2 32 64 64
      (fun i hi => fpConvert_run 32 64 (.inl ⟨rfl, rfl⟩) _ _ _ _ (hok i hi)) hm masked
  · fp_cvt_loop 2 32 128 64
      (fun i hi => fpConvert_run 32 64 (.inl ⟨rfl, rfl⟩) _ _ _ _ (hok i hi)) hm masked

end X86Proofs
