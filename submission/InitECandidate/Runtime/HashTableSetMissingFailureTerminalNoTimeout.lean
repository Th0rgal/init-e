import InitECandidate.Runtime.HashTableSetMissingFailureWidthNoTimeout
import InitECandidate.Runtime.DiscardCallNoReturn
import InitECandidate.Runtime.DiscardCallNoContinue
import InitECandidate.Runtime.HashTableArraysFindSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The live table invariant supplies all old-header reads for the original
missing-key suffix when its growth allocation plan is unsafe. -/
theorem HashTableArraysInvariant.set_missing_failure_terminal_no_timeout {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496) (clock : 7 ≤ state.clock)
    (notSafe : ¬ AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (loadFactor : capacity.toNat < (count.toNat + 1) * 2) :
    evaluateHOLFiniteState state hashSetMissing =
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_grow") [.var .local (ofString "t")]) ∧
    (evaluateHOLFiniteState state hashSetMissing).1 ≠ none ∧
    (evaluateHOLFiniteState state hashSetMissing).1 ≠ some .timeOut ∧
    (∀ output : ValueHOL 64, (evaluateHOLFiniteState state hashSetMissing).1 ≠ some (.returned output)) ∧
    (evaluateHOLFiniteState state hashSetMissing).1 ≠ some .continue ∧
    state.clock ≤ (evaluateHOLFiniteState state hashSetMissing).2.clock + 7 ∧
    (evaluateHOLFiniteState state hashSetMissing).2.clock ≤ state.clock := by
  have result := invariant.set_missing_failure_width_no_timeout state keyLength table pointer keys stride capacity used values order orderPos count bits
    heap pointerBound clock notSafe tableLocal loadFactor
  refine ⟨result.1,result.2.1,result.2.2.1,?_,?_,result.2.2.2.1,result.2.2.2.2⟩
  · intro output
    rw [result.1]
    exact evaluate_discard_call_no_return state _ _ output
  · rw [result.1]
    exact evaluate_discard_call_no_continue state _ _

#print axioms HashTableArraysInvariant.set_missing_failure_terminal_no_timeout
end InitECandidate.Runtime
