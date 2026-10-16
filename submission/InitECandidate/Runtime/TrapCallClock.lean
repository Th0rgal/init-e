import InitECandidate.Runtime.OriginalTrapCode
import InitECandidate.Runtime.TrapNoReturn
import InitECandidate.Runtime.PanSingleWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_trap_call_clock {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (value : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word value)]) :
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "trap_with") [argument])).2.clock = state.clock - 1 := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "code",.val (.word value))
  let entry := callEntryStateHOLFinite state callee
  have installed : state.code.lookup (ofString "trap_with") =
      some ([(ofString "code",.one)],sourceFunctionBody Guest.guestFn_trap_with,.one) := by
    rw [code]; exact originalRuntimeCode_trap_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "trap_with") (ofString "code")
    (sourceFunctionBody Guest.guestFn_trap_with) value installed
  have ticks := evaluate_trap_body_clock entry
  have noReturn := evaluate_trap_body_no_return entry
  rw [evaluateHOLFiniteState_call,arguments]
  dsimp only
  rw [lookup]
  dsimp only
  by_cases zero : state.clock = 0
  · simp [zero,emptyLocalsHOLFinite]
  · rw [if_neg zero]
    cases run : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_trap_with) with
    | mk result post =>
      rw [run] at ticks
      dsimp only at ticks
      have clock : post.clock = state.clock - 1 := ticks
      cases result with
      | none => exact clock
      | some result =>
        cases result <;> simp_all [emptyLocalsHOLFinite]

#print axioms evaluate_trap_call_clock
end InitECandidate.Runtime
