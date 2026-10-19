import InitECandidate.Runtime.ValidateHeadersFirstTailSource
import InitECandidate.Runtime.NormalDecCallLocalFrame
import InitECandidate.Runtime.DiscardCallSuccessLocals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual first-loop body preserves all caller bindings except its
counter and scoped header name, independently of callee internals. -/
theorem validate_headers_first_body_local_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (key : MlS) (notHeader : ofString "h" ≠ key) (notIndex : ofString "i" ≠ key)
    (run : evaluateHOLFiniteState s validateHeadersFirstBody = (none,post)) :
    post.locals.lookup key = s.locals.lookup key := by
  rw [source_validate_headers_first_decode] at run
  apply normalLocalFrame_decCall key _ _ _ _ _ notHeader ?_ s post run
  intro F state output normal
  rw [source_validate_headers_first_tail,evaluateHOLFiniteState_seq_line780] at normal
  have storeFrame := evaluate_straight_local_frame key validateHeadersHeaderStore rfl state
  cases storeRun : evaluateHOLFiniteState state validateHeadersHeaderStore with
  | mk result stored =>
    rw [storeRun] at normal storeFrame
    cases result with
    | some result => cases normal
    | none =>
      dsimp only at normal
      rw [evaluateHOLFiniteState_seq_line780] at normal
      cases hashRun : evaluateHOLFiniteState stored validateHeadersHashCall with
      | mk result hashed =>
        rw [hashRun] at normal
        cases result with
        | some result => cases normal
        | none =>
          dsimp only at normal
          have kept := evaluate_discard_call_success_locals stored (ofString "keccak256") validateHeadersHashArguments
            (by change (evaluateHOLFiniteState stored validateHeadersHashCall).1 = none; rw [hashRun])
          change (evaluateHOLFiniteState stored validateHeadersHashCall).2.locals = stored.locals at kept
          rw [hashRun] at kept
          have incrementFrame := evaluate_straight_local_frame key validateHeadersIncrement
            (by simp [validateHeadersIncrement,straightLocalFrame,notIndex]) hashed
          rw [normal] at incrementFrame
          rw [incrementFrame,kept]
          exact storeFrame

#print axioms validate_headers_first_body_local_frame
end InitECandidate.Runtime
