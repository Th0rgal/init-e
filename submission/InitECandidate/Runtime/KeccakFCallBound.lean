import InitECandidate.Runtime.OriginalKeccakFCode
import InitECandidate.Runtime.KeccakFBodyBound
import InitECandidate.Runtime.PanSingleWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem evaluate_keccakF1600_call_clock {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (value : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word value)]) :
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "keccak_f1600") [argument])).2.clock = state.clock - 1 := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "stp",.val (.word value))
  let entry := callEntryStateHOLFinite state callee
  have installed : state.code.lookup (ofString "keccak_f1600") =
      some ([(ofString "stp",.one)],sourceFunctionBody Guest.guestFn_keccak_f1600,.one) := by
    rw [code]; exact originalRuntimeCode_keccakF1600_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "keccak_f1600") (ofString "stp")
    (sourceFunctionBody Guest.guestFn_keccak_f1600) value installed
  have ticks := evaluate_keccakF1600_body_clock entry
  rw [evaluateHOLFiniteState_call,arguments]
  dsimp only
  rw [lookup]
  dsimp only
  by_cases zero : state.clock = 0
  · simp [zero,emptyLocalsHOLFinite]
  · rw [if_neg zero]
    cases run : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_keccak_f1600) with
    | mk result post =>
      rw [run] at ticks
      dsimp only at ticks
      have clock : post.clock = state.clock - 1 := ticks
      cases result with
      | none => exact clock
      | some result =>
        cases result <;> simp_all [emptyLocalsHOLFinite]
        split <;> simp_all


theorem evaluate_keccakF1600_call_no_timeout {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (value : BitVec 64)
    (clock : state.clock ≠ 0)
    (code : state.code = originalRuntimeCode)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word value)]) :
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "keccak_f1600") [argument])).1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "stp",.val (.word value))
  let entry := callEntryStateHOLFinite state callee
  have installed : state.code.lookup (ofString "keccak_f1600") =
      some ([(ofString "stp",.one)],sourceFunctionBody Guest.guestFn_keccak_f1600,.one) := by
    rw [code]; exact originalRuntimeCode_keccakF1600_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "keccak_f1600") (ofString "stp")
    (sourceFunctionBody Guest.guestFn_keccak_f1600) value installed
  have noTimeout := evaluate_keccakF1600_body_no_timeout entry
  rw [evaluateHOLFiniteState_call,arguments]
  dsimp only
  rw [lookup]
  dsimp only
  rw [if_neg clock]
  cases run : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_keccak_f1600) with
  | mk result post =>
    cases result with
    | none => simp
    | some result =>
        cases result <;> simp_all
        split <;> simp_all


#print axioms evaluate_keccakF1600_call_clock
#print axioms evaluate_keccakF1600_call_no_timeout
end InitECandidate.Runtime
