import InitECandidate.Runtime.SerializeResultBodyBound
import InitECandidate.Runtime.ByteStoresControlFrame
import InitECandidate.Runtime.DiscardCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

private theorem returned_tail {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (first tail : ProgHOL 64) (value : ValueHOL 64)
    (noReturn : (evaluateHOLFiniteState state first).1 ≠ some (.returned value))
    (run : evaluateHOLFiniteState state (.seq first tail) = (some (.returned value),post)) :
    ∃ next, evaluateHOLFiniteState next tail = (some (.returned value),post) := by
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases firstRun : evaluateHOLFiniteState state first with
  | mk result next =>
    rw [firstRun] at run noReturn
    cases result with
    | none => exact ⟨next,run⟩
    | some result => exact False.elim (noReturn (Prod.mk.inj run).1)

private theorem byte_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination expression : ExpHOL 64) (value : ValueHOL 64) :
    (evaluateHOLFiniteState state (.storeByte destination expression)).1 ≠ some (.returned value) := by
  rcases (evaluate_storeByte_control_frame state destination expression).1 with normal | error
  · rw [normal]; simp
  · rw [error]; simp

/-- Any return of the original serializer reports its exact 43-byte length,
independently of pointer readability or the success/failure fields. -/
theorem serializeResult_returned_value {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_serialize_result) =
      (some (.returned value),post)) : value = .val (.word 43) := by
  rw [source_serializeResult_body] at run
  obtain ⟨one,run⟩ := returned_tail state post serializeResultCopy _ value
    (evaluate_discard_call_no_return state _ _ value) run
  obtain ⟨two,run⟩ := returned_tail one post serializeResultSuccess _ value (byte_no_return one _ _ value) run
  obtain ⟨three,run⟩ := returned_tail two post serializeResultChain _ value
    (evaluate_discard_call_no_return two _ _ value) run
  unfold serializeResultTail at run
  obtain ⟨four,run⟩ := returned_tail three post _ _ value (byte_no_return three _ _ value) run
  obtain ⟨five,run⟩ := returned_tail four post _ _ value (byte_no_return four _ _ value) run
  have actual : evaluateHOLFiniteState five (.return (.const 43)) =
      (some (.returned (.val (.word 43))),emptyLocalsHOLFinite five) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  rw [actual] at run
  exact (PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj run).1)).symm

#print axioms serializeResult_returned_value
end InitECandidate.Runtime
