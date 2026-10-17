import InitECandidate.Runtime.RlpValidationCleanupTerminal
import InitECandidate.Runtime.PanSequenceReturnBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpValidationNormalCleanup : ProgHOL 64 :=
  .seq (.call (some (none,none)) (ofString "scratch_release") [.var .local (ofString "mark")]) (.return (.const 0))

/-- The wrapper's normal release-and-return tail spends one tick and always
terminates without timeout, including assignment failures during release. -/
theorem evaluate_rlpValidation_normal_cleanup_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (mark : BitVec 64) (markLocal : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (code : state.code = originalRuntimeCode) (ticks : state.clock ≠ 0) :
    let evaluated := evaluateHOLFiniteState state rlpValidationNormalCleanup
    evaluated.2.clock = state.clock - 1 ∧ evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  let release : ProgHOL 64 := .call (some (none,none)) (ofString "scratch_release") [.var .local (ofString "mark")]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "mark")] = some [.val (.word mark)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,markLocal]
  have bound := evaluate_scratchRelease_call_bounded state (.var .local (ofString "mark")) mark args code ticks
  have sequence := evaluate_sequence_return_zero state release
  have safe := evaluate_sequence_no_timeout state release (.return (.const 0)) bound.2
    (fun next => evaluate_straightLine_no_timeout (.return (.const 0)) (by rfl) next)
  exact ⟨sequence.1.trans bound.1,safe,sequence.2⟩

#print axioms evaluate_rlpValidation_normal_cleanup_bounded
end InitECandidate.Runtime
