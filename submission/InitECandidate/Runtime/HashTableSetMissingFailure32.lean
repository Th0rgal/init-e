import InitECandidate.Runtime.HashSetMissingAllocationFailure
import InitECandidate.Runtime.HashTableArraysFind32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The live table invariant supplies all old-header reads for the original
missing-key suffix when its growth allocation plan is unsafe. -/
theorem HashTableArraysInvariant32.set_missing_failure {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496) (clock : 5 ≤ state.clock)
    (notSafe : ¬ AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (loadFactor : capacity.toNat < (count.toNat + 1) * 2) :
    evaluateHOLFiniteState state hashSetMissing =
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_grow") [.var .local (ofString "t")]) ∧
    (evaluateHOLFiniteState state hashSetMissing).1 ≠ none ∧
    state.clock ≤ (evaluateHOLFiniteState state hashSetMissing).2.clock + 7 ∧
    (evaluateHOLFiniteState state hashSetMissing).2.clock ≤ state.clock := by
  have header := invariant.header_domain state table keys stride capacity used values order orderPos count bits
  have capacityBound : capacity.toNat ≤ 33806089496 := by
    have usedBefore := invariant.usedBefore
    have orderBefore := invariant.orderBefore
    have limit := invariant.endBound
    omega
  exact evaluate_hashSet_missing_allocation_failure state table capacity stride keys values order count
    (header 16 (by decide)) invariant.cell16 (header 8 (by decide)) invariant.cell8
    (header 32 (by decide)) invariant.cell32 (header 40 (by decide)) invariant.cell40
    (header 56 (by decide)) invariant.cell56 (header 24 (by decide)) invariant.cell24
    pointer invariant.code heap pointerBound clock notSafe tableLocal loadFactor invariant.room capacityBound

#print axioms HashTableArraysInvariant32.set_missing_failure
end InitECandidate.Runtime
