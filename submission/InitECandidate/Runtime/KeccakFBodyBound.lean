import InitECandidate.Runtime.TrapBodyClock
import InitECandidate.Runtime.TrapNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_keccakF1600_body : sourceFunctionBody Guest.guestFn_keccak_f1600 =
    .seq (.extCall (ofString "keccakf") (.var .local (ofString "stp")) (.const 0)
      (.var .local (ofString "stp")) (.const 200)) (.return (.const 0)) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original external Keccak permutation body consumes no source clock,
including early errors and final-FFI results. -/
theorem evaluate_keccakF1600_body_clock {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_keccak_f1600)).2.clock = state.clock := by
  rw [source_keccakF1600_body]
  apply evaluate_sequence_preserves_clock
  · exact evaluate_external_call_clock _ _ _ _ _ _
  · intro next
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,emptyLocalsHOLFinite]

/-- External Keccak outcomes and the literal return cannot produce timeout. -/
theorem evaluate_keccakF1600_body_no_timeout {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_keccak_f1600)).1 ≠ some .timeOut := by
  rw [source_keccakF1600_body]
  apply evaluate_sequence_no_timeout
  · exact evaluate_external_call_no_timeout _ _ _ _ _ _
  · intro next
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]

#print axioms source_keccakF1600_body
#print axioms evaluate_keccakF1600_body_clock
#print axioms evaluate_keccakF1600_body_no_timeout
end InitECandidate.Runtime
