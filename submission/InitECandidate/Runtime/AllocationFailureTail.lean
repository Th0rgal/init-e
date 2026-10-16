import InitECandidate.Runtime.AllocationRequestFailure
import InitECandidate.Runtime.TrapCallTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_sequence_stops {F : Type} (state : PanSemStateFiniteExact 64 F)
    (first second : ProgHOL 64)
    (terminal : (evaluateHOLFiniteState state first).1 ≠ none)
    (bounded : (evaluateHOLFiniteState state first).2.clock ≤ state.clock) :
    evaluateHOLFiniteState state (.seq first second) = evaluateHOLFiniteState state first := by
  have fixed : fixClockHOLFinite state (evaluateHOLFiniteState state first) = evaluateHOLFiniteState state first := by
    simp [fixClockHOLFinite,Nat.not_lt.mpr bounded]
  rw [evaluateHOLFiniteState_seq]
  dsimp only
  rw [fixed]
  split
  · contradiction
  · rfl

/-- The original allocator's excessive-request path runs the trap and skips
pointer rounding, heap assignment, and the successful return. -/
theorem evaluate_allocationAfterPointer_failure {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer size : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (request : ((33806089496 : BitVec 64) - pointer).toNat < size.toNat) :
    evaluateHOLFiniteState state allocationAfterPointer =
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "trap_with") [.const 1]) ∧
    (evaluateHOLFiniteState state allocationAfterPointer).2.clock = state.clock - 1 ∧
    (evaluateHOLFiniteState state allocationAfterPointer).1 ≠ none := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const 1] = some [.val (.word (1 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
  have ticks := evaluate_trap_call_clock state (.const 1) 1 code arguments
  have terminal := evaluate_trap_call_terminal state (.const 1) 1 code arguments
  have selected := evaluate_allocationRequest_failure_selected state pointer size pointerLocal sizeLocal request
  have stopped := evaluate_sequence_stops state
    (.ite allocationRequestCheck (.call (some (none,none)) (ofString "trap_with") [.const 1]) .skip)
    (.dec (ofString "q") .one allocationEndExpression allocationFinish)
    (by rw [selected]; exact terminal) (by rw [selected,ticks]; omega)
  have exactRun : evaluateHOLFiniteState state allocationAfterPointer =
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "trap_with") [.const 1]) := stopped.trans selected
  exact ⟨exactRun,by rw [exactRun]; exact ticks,by rw [exactRun]; exact terminal⟩

#print axioms evaluate_sequence_stops
#print axioms evaluate_allocationAfterPointer_failure
end InitECandidate.Runtime
