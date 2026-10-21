import InitECandidate.Runtime.StackNativeLocalPrice
import InitECandidate.Runtime.StackExecutionCostProps
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabSem

/-- Small numeric instruction prices once the artifact's local gap is certified. -/
noncomputable def nativePriceWithGap (gap : Nat) (p : HolProg 64) : Nat :=
  match p with
  | .inst instruction => instLocalCost instruction + gap
  | .tick => instLocalCost .skip + gap
  | .locValue _ _ _ => 2 + gap
  | .break _ => 2
  | .ret _ | .raise _ | .shMemOp _ _ _ => 1
  | .ffi _ _ _ _ _ _ => 19 + gap
  | .ite _ _ _ _ _ => 5 + gap
  | .loop _ => 2
  | .call none dest _ => callJumpWork dest
  | .call (some _) dest _ => 4 + gap + callJumpWork dest
  | .rawCall _ => 2
  | .jumpLower _ _ _ => 3 + gap
  | _ => 0

theorem nativeLocalPrice_le {F : Type} (gap : Nat) (encoded : LabProgHOL 64)
    (bounded : encodedLineWords encoded ≤ gap) (p : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    nativeLocalPrice p source encoded ≤ nativePriceWithGap gap p := by
  cases p <;> try (simp only [nativeLocalPrice, nativePriceWithGap]; omega)
  case call ret dest handler =>
    cases ret <;> simp only [nativeLocalPrice, nativePriceWithGap] <;> omega

/-- The concrete local coefficient passes through the entire actual execution
without multiplying by call depth or program size. -/
theorem stackExecutionCost_nativePriceWithGap {F : Type} (gap : Nat) (encoded : LabProgHOL 64)
    (bounded : encodedLineWords encoded ≤ gap) (p : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p s => nativeLocalPrice p s encoded) p source ≤
      stackExecutionCost (fun p _ => nativePriceWithGap gap p) p source :=
  stackExecutionCost_mono _ _ (nativeLocalPrice_le gap encoded bounded) p source

#print axioms nativeLocalPrice_le
#print axioms stackExecutionCost_nativePriceWithGap
end InitECandidate.Runtime.StackToLab
