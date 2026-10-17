import InitECandidate.Runtime.StateFreshTxFieldLoads
import InitECandidate.Runtime.HashTablePhysicalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A mutation confined to a later table's live regions preserves all eight
transaction field cells, including when the table arrays have moved. -/
theorem StateFreshTxFields.after_table_physical_frame {F : Type}
    (state post : PanSemStateFiniteExact 64 F)
    (ts fieldPointer keyLength table pointer keys stride capacity used values order reverse items : BitVec 64) (bits : Nat)
    (fields : StateFreshTxFields ts fieldPointer stateFreshTxAllTables state)
    (ready : HashTableReady keyLength table keys stride capacity used values order reverse items bits pointer state)
    (headerBefore : ts.toNat + 72 ≤ table.toNat)
    (frame : ∀ address : BitVec 64, ¬tablePhysicalRegion table keys stride capacity used values order reverse address →
      post.memory address = state.memory address) :
    StateFreshTxFields ts fieldPointer stateFreshTxAllTables post := by
  have headerKeys := ready.live.arrays.headerKeys
  have headerValues := ready.live.arrays.headerValues
  have keysBefore := ready.live.arrays.keysBefore
  have valuesBefore := ready.live.arrays.valuesBefore
  have usedBefore := ready.live.arrays.usedBefore
  have orderBefore := ready.live.arrays.orderBefore
  have endBound := ready.live.arrays.endBound
  intro binding member
  rcases binding with ⟨offset,fieldTable⟩
  have offsets := List.mem_map_of_mem (f := Prod.fst) member
  rw [stateFreshTx_table_binding_offsets] at offsets
  have small : offset < 72 := by simp at offsets; omega
  have natural : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
  have address : (ts + BitVec.ofNat 64 offset).toNat = ts.toNat + offset := by
    rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
  have outside : ¬tablePhysicalRegion table keys stride capacity used values order reverse (ts + BitVec.ofNat 64 offset) := by
    unfold tablePhysicalRegion
    rw [address]
    omega
  exact (frame _ outside).trans (fields (offset,fieldTable) member)

#print axioms StateFreshTxFields.after_table_physical_frame
end InitECandidate.Runtime
