import InitECandidate.Runtime.RunBounded
import InitECandidate.Runtime.AvoidsLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem runBounded_discard_heap_seq {F : Type} (state : PanSemStateFiniteExact 64 F)
    (function : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64) (heapKey : MlS) (heap : BitVec 64)
    (firstCost tailCost : Nat)
    (first : RunBounded state (.call (some (none,none)) function arguments) firstCost)
    (budget : firstCost + tailCost ≤ state.clock)
    (heapFrame : ∀ next, evaluateHOLFiniteState state (.call (some (none,none)) function arguments) = (none,next) →
      next.globals.lookup heapKey = some (.val (.word heap)))
    (rest : ∀ next : PanSemStateFiniteExact 64 F, (∀ key, next.locals.lookup key = state.locals.lookup key) →
      next.globals.lookup heapKey = some (.val (.word heap)) → next.code = state.code → tailCost ≤ next.clock →
      RunBounded next tail tailCost) :
    RunBounded state (.seq (.call (some (none,none)) function arguments) tail) (firstCost + tailCost) := by
  refine RunBounded.seq first budget ?_
  intro next normal code remaining
  apply rest next ?_ (heapFrame next normal) code remaining
  intro key
  have frame := evaluate_avoidsLocal_flowing key (.call (some (none,none)) function arguments) rfl state
    (by rw [normal]; exact Or.inl rfl)
  simpa only [normal] using frame

#print axioms runBounded_discard_heap_seq
end InitECandidate.Runtime
