import InitECandidate.Runtime.SourceBoundFromExpanded
import InitECandidate.Runtime.OriginalMainCode
import InitECandidate.Runtime.PanNoArgsLookup
import InitECandidate.Runtime.PanTailCallNoTimeout
import InitECandidate.Runtime.MainSszHandlerSource
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem expanded_main_call_non_timeout_of_body (input : Guest.InputBlob) (bodyFuel : Nat)
    (safe : (evaluateHOLFiniteState {expandedRuntimeEntry input with clock:=bodyFuel}
      (mainAt 0)).1≠some .timeOut) :
    (evaluateHOLFiniteState {expandedRuntimeEntry input with clock:=bodyFuel+1}
      (.call none (ofString "main") [])).1≠some .timeOut := by
  let state := {expandedRuntimeEntry input with clock:=bodyFuel+1}
  have locals : (expandedRuntimeEntry input).locals=HolFiniteMapExact.empty := by
    change (canonicalOriginalSourceEntry input).locals=_
    rw [canonical_original_source_fields]
    rfl
  have entry : callEntryStateHOLFinite state HolFiniteMapExact.empty=
      {expandedRuntimeEntry input with clock:=bodyFuel} := by
    change {expandedRuntimeEntry input with locals:=HolFiniteMapExact.empty,clock:=bodyFuel+1-1}=_
    simp only [Nat.add_sub_cancel]
    rw [←locals]
  have lookup := pan_no_args_lookup state.code.lookup (ofString "main")
    (sourceFunctionBody Guest.guestFn_main) (by
      change (canonicalOriginalSourceEntry input).code.lookup _=_
      rw [canonical_original_source_code]
      exact originalRuntimeCode_main_lookup)
  cases run : evaluateHOLFiniteState (callEntryStateHOLFinite state HolFiniteMapExact.empty)
      (sourceFunctionBody Guest.guestFn_main) with
  | mk result post =>
    apply evaluate_tailCall_no_timeout state post (ofString "main") [] []
      (sourceFunctionBody Guest.guestFn_main) HolFiniteMapExact.empty .one result
      (by rfl) lookup (by change bodyFuel+1≠0; omega) run
    rw [entry] at run
    change (evaluateHOLFiniteState {expandedRuntimeEntry input with clock:=bodyFuel}
      (sourceFunctionBody Guest.guestFn_main)).1≠some .timeOut at safe
    simpa only [run] using safe

/-- A finite bound on the proof main body closes the unchanged source
certificate, including the one tick required to enter main. -/
theorem sourceBound_of_expanded_main_body_non_timeout (bodyBound : Guest.InputBlob→Nat)
    (safe : ∀ input, Guest.GasLimit.declaredGasLimit input≤200000000→
      (evaluateHOLFiniteState {expandedRuntimeEntry input with clock:=bodyBound input}
        (mainAt 0)).1≠some .timeOut) : SourceBound (fun input=>bodyBound input+1) := by
  apply sourceBound_of_expanded_non_timeout
  intro input gas
  exact expanded_main_call_non_timeout_of_body input (bodyBound input) (safe input gas)

#print axioms expanded_main_call_non_timeout_of_body
#print axioms sourceBound_of_expanded_main_body_non_timeout
end InitECandidate.Runtime
