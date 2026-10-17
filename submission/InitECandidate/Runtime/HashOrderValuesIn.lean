import InitECandidate.Runtime.HashOrderLinkedComplete
import InitECandidate.Runtime.HashTableValuesIn
import InitECandidate.Runtime.HashGrowOldArrays
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Every value selected by a live order entry belongs to the target registry.
This remains meaningful after growth replaces the table header's array pointers. -/
def HashOrderValuesIn {F : Type} (order values items : BitVec 64) (targets : Set (BitVec 64))
    (state : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ position : BitVec 64, position.toNat < items.toNat → ∀ slot : BitVec 64,
    state.memory (order + position * 8) = .word slot → ∀ value : BitVec 64,
      state.memory (values + slot * 8) = .word value → value ∈ targets

/-- The existing complete table invariant derives order-selected membership
from occupied-value membership; no new reachability premise is required. -/
theorem HashTableReady.order_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos items pointer : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state) :
    HashOrderValuesIn order values items targets state := by
  intro position inside slot orderCell value valueCell
  obtain ⟨actual,slotInside,occupied,forward⟩ := ready.linked.order_occupied state used order orderPos capacity items ready.live.arrays.agreement position inside
  have same : actual = slot := by simpa only [HolWordLab.word.injEq] using forward.symm.trans orderCell
  subst actual
  exact entries capacity used values ready.live.arrays.cell16 ready.live.arrays.cell48 ready.live.arrays.cell40 slot slotInside occupied value valueCell

/-- Read-only execution retains the old order/value relation. -/
theorem HashOrderValuesIn.after_memory {F : Type} {state post : PanSemStateFiniteExact 64 F}
    {order values items : BitVec 64} {targets : Set (BitVec 64)}
    (entries : HashOrderValuesIn order values items targets state) (memory : post.memory = state.memory) :
    HashOrderValuesIn order values items targets post := by
  intro position inside slot orderCell value valueCell
  rw [memory] at orderCell valueCell
  exact entries position inside slot orderCell value valueCell

/-- The existing rehash earlier-region frame retains every old order-selected
registered value, including relocated old arrays. -/
theorem HashOrderValuesIn.preserved {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (table keys stride values order capacity items : BitVec 64) (frontier : Nat)
    (old : HashGrowOldArrays table keys stride values order capacity items frontier state)
    (targets : Set (BitVec 64)) (entries : HashOrderValuesIn order values items targets state)
    (headerValues : table.toNat + 72 ≤ values.toNat)
    (valuesEnd : values.toNat + capacity.toNat * 8 ≤ frontier)
    (frame : ∀ watched : BitVec 64, table.toNat + 72 ≤ watched.toNat → watched.toNat < frontier → post.memory watched = state.memory watched) :
    HashOrderValuesIn order values items targets post := by
  intro position inside slot orderCell value valueCell
  have positionInside : position.toNat < capacity.toNat := by have bound := old.itemsBound; omega
  have orderAddress := (hashFind_slot_address order position 8 capacity positionInside old.orderBound old.orderAligned (by decide)).1
  change (order + position * 8).toNat = order.toNat + position.toNat * 8 at orderAddress
  have orderProduct := Nat.mul_lt_mul_of_pos_right positionInside (by decide : 0 < 8)
  have orderFrame := frame (order + position * 8) (by have lower := old.headerOrder; omega) (by have upper := old.orderEnd; omega)
  have beforeCell := orderFrame.symm.trans orderCell
  obtain ⟨actual,actualCell,slotInside⟩ := old.entries position inside
  have same : actual = slot := by simpa only [HolWordLab.word.injEq] using actualCell.symm.trans beforeCell
  subst actual
  have valueAddress := (hashFind_slot_address values slot 8 capacity slotInside old.valueBound old.valuesAligned (by decide)).1
  change (values + slot * 8).toNat = values.toNat + slot.toNat * 8 at valueAddress
  have valueProduct := Nat.mul_lt_mul_of_pos_right slotInside (by decide : 0 < 8)
  have valueFrame := frame (values + slot * 8) (by omega) (by omega)
  exact entries position inside slot beforeCell value (valueFrame.symm.trans valueCell)

#print axioms HashTableReady.order_values_in
#print axioms HashOrderValuesIn.after_memory
#print axioms HashOrderValuesIn.preserved
end InitECandidate.Runtime
