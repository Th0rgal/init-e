import InitECandidate.Runtime.RlpValidationNormalCleanup
import InitECandidate.Runtime.ScratchReleaseSuccessful
import InitECandidate.Runtime.DiscardCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful normal cleanup restores scratch_ptr exactly and changes no
other globals; the discarded release call cannot bypass the final return. -/
theorem rlpValidation_normal_cleanup_returned_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (mark : BitVec 64) (value : ValueHOL 64)
    (markLocal : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state rlpValidationNormalCleanup = (some (.returned value),post)) :
    post.globals = (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word mark)) state).globals := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "mark")] = some [.val (.word mark)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,markLocal]
  rw [rlpValidationNormalCleanup,evaluateHOLFiniteState_seq_line780] at run
  cases releaseRun : evaluateHOLFiniteState state
      (.call (some (none,none)) (ofString "scratch_release") [.var .local (ofString "mark")]) with
  | mk result next =>
    rw [releaseRun] at run
    cases result with
    | none =>
      have released := scratchRelease_normal_globals state next (.var .local (ofString "mark")) mark args code releaseRun
      have actual : evaluateHOLFiniteState next (.return (.const 0)) =
          (some (.returned (.val (.word 0))),emptyLocalsHOLFinite next) := by
        simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
      have same := (Prod.mk.inj (run.symm.trans actual)).2
      rw [same]
      exact released.1
    | some result =>
      have impossible := evaluate_discard_call_no_return state (ofString "scratch_release") [.var .local (ofString "mark")] value
      rw [releaseRun] at impossible
      exact False.elim (impossible (Prod.mk.inj run).1)

#print axioms rlpValidation_normal_cleanup_returned_globals
end InitECandidate.Runtime
