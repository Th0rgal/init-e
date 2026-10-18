import InitECandidate.Runtime.SszFailCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An actual ssz_fail call never produces loop-control results. -/
theorem evaluate_sszFail_call_not_control {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (value : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word value)]) :
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "ssz_fail") [argument])).1 ≠ some .break ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "ssz_fail") [argument])).1 ≠ some .continue := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "code",.val (.word value))
  let entry := callEntryStateHOLFinite state callee
  have installed : state.code.lookup (ofString "ssz_fail") =
      some ([(ofString "code",.one)],sourceFunctionBody Guest.guestFn_ssz_fail,.one) := by
    rw [code]; exact originalRuntimeCode_sszFail_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "ssz_fail") (ofString "code")
    (sourceFunctionBody Guest.guestFn_ssz_fail) value installed
  have noReturn := fun v => evaluate_sszFail_body_no_return entry v
  rw [evaluateHOLFiniteState_call,arguments]
  dsimp only
  rw [lookup]
  dsimp only
  by_cases zero : state.clock = 0
  · simp [zero]
  · rw [if_neg zero]
    cases run : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_ssz_fail) with
    | mk result post =>
      cases result with
      | none => simp
      | some result =>
        cases result <;> simp_all

#print axioms evaluate_sszFail_call_not_control
end InitECandidate.Runtime
