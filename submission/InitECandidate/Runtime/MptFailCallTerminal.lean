import InitECandidate.Runtime.MptFailCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original mpt_fail never falls through, including when no call clock remains. -/
theorem evaluate_mptFail_call_terminal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (value : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [argument] = some [.val (.word value)]) :
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "mpt_fail") [argument])).1 ≠ none := by
  by_cases zero : state.clock = 0
  · let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "code",.val (.word value))
    let entry := callEntryStateHOLFinite state callee
    have installed : state.code.lookup (ofString "mpt_fail") =
        some ([(ofString "code",.one)],sourceFunctionBody Guest.guestFn_mpt_fail,.one) := by
      rw [code]; exact originalRuntimeCode_mptFail_lookup
    have lookup := pan_single_word_lookup state.code.lookup (ofString "mpt_fail") (ofString "code")
      (sourceFunctionBody Guest.guestFn_mpt_fail) value installed
    rw [evaluateHOLFiniteState_call,arguments]
    dsimp only
    rw [lookup]
    simp [zero]
  · exact (evaluate_mptFail_call_bounded state argument value code zero arguments).2.2

#print axioms evaluate_mptFail_call_terminal
end InitECandidate.Runtime
