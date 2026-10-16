import InitECandidate.Runtime.HashTableArraysInvariant32
import InitECandidate.Runtime.HashGrowOldArrays
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A live table with valid order entries supplies the old-array precondition
for actual growth when its allocations precede the next heap pointer. -/
theorem HashTableArraysInvariant32.old_arrays {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count : BitVec 64)
    (bits frontier : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (entries : HashOrderEntriesBound order capacity count state)
    (allocated : orderPos.toNat + capacity.toNat * 8 ≤ frontier)
    (bounded : frontier ≤ 33806089496) :
    HashGrowOldArrays table keys stride values order capacity count frontier state := by
  have hk := invariant.headerKeys
  have hv := invariant.headerValues
  have ku := invariant.keysBefore
  have vu := invariant.valuesBefore
  have uo := invariant.usedBefore
  have orr := invariant.orderBefore
  have limit := invariant.endBound
  exact {
    keysAligned := invariant.keysAligned
    valuesAligned := invariant.valuesAligned
    orderAligned := invariant.orderAligned
    keyBound := by omega
    valueBound := by omega
    orderBound := by omega
    headerOrder := by omega
    orderEnd := by omega
    frontierBound := bounded
    itemsBound := Nat.le_of_lt invariant.room
    keyDomain := by
      intro address lower upper
      apply invariant.domain <;> omega
    valueDomain := by
      intro address lower upper
      apply invariant.domain <;> omega
    orderDomain := by
      intro address lower upper
      apply invariant.domain <;> omega
    entries := entries
  }

#print axioms HashTableArraysInvariant32.old_arrays
end InitECandidate.Runtime
