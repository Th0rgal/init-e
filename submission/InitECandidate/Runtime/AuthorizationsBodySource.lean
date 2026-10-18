import InitECandidate.Runtime.AuthorizationsAllocationBound
import InitECandidate.Runtime.PanDecCallTerminal
import InitECandidate.Runtime.PanSequenceTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_authorization_body : sourceFunctionBody Guest.guestFn_decode_authorizations =
    .decCall (ofString "lst") (.comb [.one,.one]) (ofString "rlp_list_to_slices")
      [.var .local (ofString "p"),.var .local (ofString "len")] authorizationAfterSlices := by
  simp only [authorizationAfterSlices,authorizationAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- All original authorization-decoder scopes terminate through return or an error,
including malformed arguments, failed allocation and exhausted clocks. -/
theorem evaluate_authorization_body_terminal {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_authorizations)).1 ≠ none := by
  rw [source_authorization_body]
  apply evaluate_decCall_terminal
  intro current
  rw [source_authorization_allocation]
  apply evaluate_decCall_terminal
  intro ready
  have terminal : ∀ current : PanSemStateFiniteExact 64 F,
      (evaluateHOLFiniteState current authorizationLoopAndReturn).1 ≠ none := by
    intro current
    rw [source_authorization_loop_and_return]
    exact evaluate_seq_terminal current _ _ (fun output => evaluate_return_terminal output _)
  rw [source_authorization_initialized,evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  cases run : evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) ready) authorizationLoopAndReturn with
  | mk result post =>
    have stopped := terminal (setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) ready)
    rw [run] at stopped
    exact stopped

#print axioms evaluate_authorization_body_terminal
end InitECandidate.Runtime
