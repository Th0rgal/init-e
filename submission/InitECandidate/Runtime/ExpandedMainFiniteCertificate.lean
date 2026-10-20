import InitECandidate.Runtime.ExpandedMainCallBoundReduction
import InitECandidate.Runtime.BaselineFiniteCertificate
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The remaining analytic obligation for a finite baseline submission:
non-timeout of the whole expanded main body at one uniform finite clock.
The domain bridge, entry tick, compiler scaling and bootstrap are composed
here, without changing the challenge or assuming a source execution. -/
theorem baseline_finite_certificate_of_expanded_main (bodyCeiling : Nat)
 (safe : ∀ input, Guest.GasLimit.declaredGasLimit input≤200000000→
  (evaluateHOLFiniteState {expandedRuntimeEntry input with clock:=bodyCeiling}
   (mainAt 0)).1≠some .timeOut) :
 Certificate
  (withScore baselineSubmission
   (.finite (sourceNativeSlope*(bodyCeiling+1)+(sourceNativeOffset+46240))))
  (.finite (sourceNativeSlope*(bodyCeiling+1)+(sourceNativeOffset+46240))) := by
 apply baseline_finite_certificate_of_source_bound (fun _=>bodyCeiling+1) (bodyCeiling+1)
 · exact sourceBound_of_expanded_main_body_non_timeout (fun _=>bodyCeiling) safe
 · intro input gas
   exact Nat.le_refl _

#print axioms baseline_finite_certificate_of_expanded_main
end InitECandidate.Runtime
