import InitECandidate.Runtime.HashValueEntriesWord
import InitECandidate.Runtime.HashTableArraysRead32
import InitECandidate.Runtime.HashFindArguments
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- An occupied scanned slot has a concrete word value, and both the source
value load and destination value store lie in the allocated table domain. -/
theorem HashTableArraysInvariant32.delete_value_ready {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count hole scan : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (words : HashValueEntriesWord used values capacity state)
    (holeInside : hole.toNat < capacity.toNat) (scanInside : scan.toNat < capacity.toNat)
    (occupied : hashOccupancyRead state used scan ≠ some 0) :
    ∃ value : BitVec 64, state.memory (values + scan * 8) = .word value ∧
      state.memaddrs (values + scan * 8) ∧ state.memaddrs (values + hole * 8) := by
  obtain ⟨value,cell⟩ := words scan scanInside occupied
  have hv := invariant.headerValues
  have vu := invariant.valuesBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have limit := invariant.endBound
  have available : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → state.memaddrs (values + slot * 8) := by
    intro slot inside
    have address := (hashFind_slot_address values slot 8 capacity inside
      (by change values.toNat + capacity.toNat * 8 ≤ 33806089496; omega)
      invariant.valuesAligned (by decide)).1
    change (values + slot * 8).toNat = values.toNat + slot.toNat * 8 at address
    have product := Nat.mul_lt_mul_of_pos_right inside (by decide : 0 < 8)
    apply invariant.domain <;> omega
  exact ⟨value,cell,available scan scanInside,available hole holeInside⟩

#print axioms HashTableArraysInvariant32.delete_value_ready
end InitECandidate.Runtime
