import InitECandidate.Runtime.ScratchReleaseCall
import InitECandidate.Runtime.DiscardCallNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Release costs one call tick even if scratch_ptr has the wrong shape and
its assignment fails. No scratch-global premise is needed for this bound. -/
theorem evaluate_scratchRelease_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (mark : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
      some [.val (.word mark)])
    (code : state.code = originalRuntimeCode) (ticks : state.clock ≠ 0) :
    let evaluated := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "scratch_release") [argument])
    evaluated.2.clock = state.clock - 1 ∧ evaluated.1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "m",.val (.word mark))
  let entry := callEntryStateHOLFinite state callee
  have supported : straightLine (sourceFunctionBody Guest.guestFn_scratch_release) = true := by
    rw [source_scratch_release]; rfl
  have cost := clockPreserving_of_straightLine _ supported entry
  have safe := evaluate_straightLine_no_timeout _ supported entry
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_scratch_release) with
  | mk bodyResult bodyPost =>
    rw [bodyRun] at cost safe
    have installed : state.code.lookup (ofString "scratch_release") =
        some ([(ofString "m",.one)],sourceFunctionBody Guest.guestFn_scratch_release,.one) := by
      rw [code]; exact originalRuntimeCode_scratchRelease_lookup
    have lookup := pan_single_word_lookup state.code.lookup (ofString "scratch_release") (ofString "m")
      (sourceFunctionBody Guest.guestFn_scratch_release) mark installed
    have clock := evaluate_discard_call_body_clock state bodyPost (ofString "scratch_release") [argument]
      [.val (.word mark)] (sourceFunctionBody Guest.guestFn_scratch_release) callee .one bodyResult args lookup ticks bodyRun
    have noTimeout := evaluate_discard_call_body_no_timeout state bodyPost (ofString "scratch_release") [argument]
      [.val (.word mark)] (sourceFunctionBody Guest.guestFn_scratch_release) callee .one bodyResult args lookup ticks bodyRun safe
    exact ⟨clock.trans cost,noTimeout⟩

#print axioms evaluate_scratchRelease_call_bounded
end InitECandidate.Runtime
