import InitECandidate.Runtime.PanDomainEvaluation
import InitECandidate.Runtime.ExpandedRuntimeDomain
import InitECandidate.Runtime.SourceFuelFromNonTimeout
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An actual canonical timeout would persist in the enlarged proof domain. -/
theorem canonical_main_non_timeout_of_expanded (input : Guest.InputBlob) (fuel : Nat)
    (safe : (evaluateHOLFiniteState {expandedRuntimeEntry input with clock:=fuel}
      (.call none (ofString "main") [])).1≠some .timeOut) :
    (evaluateHOLFiniteState {canonicalOriginalSourceEntry input with clock:=fuel}
      (.call none (ofString "main") [])).1≠some .timeOut := by
  intro timeout
  have nonerror : (evaluateHOLFiniteState {canonicalOriginalSourceEntry input with clock:=fuel}
      (.call none (ofString "main") [])).1≠some .error := by
    rw [timeout]
    intro impossible
    cases impossible
  have preserved := evaluateHOLFiniteState_memaddrs_mono
    {canonicalOriginalSourceEntry input with clock:=fuel}
    (.call none (ofString "main") []) (fun address=>address.toNat<heapEnd)
    (fun address member=>expanded_runtime_domain_contains input address member) nonerror
  have result := congrArg Prod.fst preserved
  change (evaluateHOLFiniteState {expandedRuntimeEntry input with clock:=fuel}
    (.call none (ofString "main") [])).1=_ at result
  exact safe (result.trans timeout)

/-- The proof domain is sufficient for the unchanged challenge SourceBound. -/
theorem sourceBound_of_expanded_non_timeout (bound : Guest.InputBlob→Nat)
    (safe : ∀ input, Guest.GasLimit.declaredGasLimit input≤200000000 →
      (evaluateHOLFiniteState {expandedRuntimeEntry input with clock:=bound input}
        (.call none (ofString "main") [])).1≠some .timeOut) : SourceBound bound := by
  apply sourceBound_of_canonical_non_timeout bound
  intro input gas
  exact canonical_main_non_timeout_of_expanded input (bound input) (safe input gas)

#print axioms canonical_main_non_timeout_of_expanded
#print axioms sourceBound_of_expanded_non_timeout
end InitECandidate.Runtime
