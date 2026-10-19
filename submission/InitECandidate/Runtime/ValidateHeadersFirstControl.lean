import InitECandidate.Runtime.ValidateHeadersFirstTailSource
import InitECandidate.Runtime.NoLoopControlStores
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Callee break/continue are converted at call boundaries, so neither can
escape the actual validation iteration into its surrounding loop. -/
theorem validate_headers_first_body_no_loop_control {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s validateHeadersFirstBody).1 ≠ some .continue ∧
    (evaluateHOLFiniteState s validateHeadersFirstBody).1 ≠ some .break := by
  have supported : noLoopControlStores validateHeadersFirstBody = true := by
    rw [source_validate_headers_first_decode]
    change noLoopControlStores validateHeadersFirstTail = true
    rw [source_validate_headers_first_tail]
    rfl
  exact (evaluate_noLoopControlStores validateHeadersFirstBody supported s).symm

#print axioms validate_headers_first_body_no_loop_control
end InitECandidate.Runtime
