import InitECandidate.Runtime.RlpFailCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- RLP failure never falls through, even when no source tick remains. -/
theorem evaluate_rlpFail_call_terminal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (value : BitVec 64) (code : state.code = originalRuntimeCode)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [argument] = some [.val (.word value)]) :
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_fail") [argument])).1 ≠ none := by
  by_cases zero : state.clock = 0
  · have installed : state.code.lookup (ofString "rlp_fail") =
        some ([(ofString "code",.one)],sourceFunctionBody Guest.guestFn_rlp_fail,.one) := by
      rw [code]; exact originalRuntimeCode_rlpFail_lookup
    have lookup := pan_single_word_lookup state.code.lookup (ofString "rlp_fail") (ofString "code")
      (sourceFunctionBody Guest.guestFn_rlp_fail) value installed
    rw [evaluateHOLFiniteState_call,args]
    dsimp only
    rw [lookup]
    simp [zero]
  · exact (evaluate_rlpFail_call_bounded state argument value code zero args).2.2

#print axioms evaluate_rlpFail_call_terminal
end InitECandidate.Runtime
