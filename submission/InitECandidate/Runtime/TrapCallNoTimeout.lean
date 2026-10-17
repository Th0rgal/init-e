import InitECandidate.Runtime.TrapCallTerminal
import InitECandidate.Runtime.TrapNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_trap_call_no_timeout {F : Type} (state : PanSemStateFiniteExact 64 F)
    (argument : ExpHOL 64) (value : BitVec 64)
    (clock : state.clock ≠ 0)
    (code : state.code = originalRuntimeCode)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word value)]) :
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "trap_with") [argument])).1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "code",.val (.word value))
  let entry := callEntryStateHOLFinite state callee
  have installed : state.code.lookup (ofString "trap_with") =
      some ([(ofString "code",.one)],sourceFunctionBody Guest.guestFn_trap_with,.one) := by
    rw [code]; exact originalRuntimeCode_trap_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "trap_with") (ofString "code")
    (sourceFunctionBody Guest.guestFn_trap_with) value installed
  have noReturn := evaluate_trap_body_no_return entry
  have noTimeout := evaluate_trap_body_no_timeout entry
  rw [evaluateHOLFiniteState_call,arguments]
  dsimp only
  rw [lookup]
  dsimp only
  rw [if_neg clock]
  cases run : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_trap_with) with
  | mk result post =>
    cases result with
    | none => simp
    | some result => cases result <;> simp_all

#print axioms evaluate_trap_call_no_timeout
end InitECandidate.Runtime
