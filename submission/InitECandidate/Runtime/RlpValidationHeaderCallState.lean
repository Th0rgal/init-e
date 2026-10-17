import InitECandidate.Runtime.RlpValidationHeaderCall
import InitECandidate.Runtime.RlpHeaderCallState
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original validator header call exposes its actual continuation with
caller locals and memory preserved and checked header progress and size facts. -/
theorem evaluate_rlpValidation_header_call_state {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (position stop : BitVec 64)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (code : state.code = originalRuntimeCode) (ticks : 12 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpValidationHeaderCall = (none,post)) :
    ∃ (value : ValueHOL 64) (ready output : PanSemStateFiniteExact 64 F),
      RlpHeaderSizedProgress value (stop - position) ∧ ready.locals = state.locals ∧ ready.memory = state.memory ∧
      ready.globals = state.globals ∧ ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧
      ready.clock ≤ state.clock ∧ state.clock ≤ ready.clock + 12 ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString "h") value ready) rlpValidationHeaderContinuation = (none,output) ∧
      post = {output with locals := HolFiniteMapExact.resVarEq output.locals (ofString "h",state.locals.lookup (ofString "h"))} := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "pos"),.op .sub [.var .local (ofString "end"),.var .local (ofString "pos")]] =
      some [.val (.word position),.val (.word (stop - position))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,positionLocal,stopLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpValidation_header_call] at run
  exact evaluate_rlpHeader_decCall_normal_state state post (ofString "h")
    [.var .local (ofString "pos"),.op .sub [.var .local (ofString "end"),.var .local (ofString "pos")]]
    rlpValidationHeaderContinuation position (stop - position) args code ticks run

#print axioms evaluate_rlpValidation_header_call_state
end InitECandidate.Runtime
