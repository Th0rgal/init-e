import InitECandidate.Runtime.HashTableValuesInInsertStores
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Clearing the final hole's actual occupancy byte preserves registered
values, including neighboring occupancy bytes in the same aligned word. -/
theorem HashTableValuesIn.clear_occupancy {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count index cell : BitVec 64) (bits : Nat)
    (arrays : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state)
    (inside : index.toNat < capacity.toNat)
    (cellMemory : state.memory (panByteAlignHOL (used + index)) = .word cell)
    (domain : state.memaddrs (panByteAlignHOL (used + index))) :
    HashTableValuesIn table targets (sourceWriteByte state (used + index) 0 cell) := by
  obtain ⟨_,byteValues,_⟩ := arrays.insert_value_separation_width state keyLength table keys stride capacity used values order orderPos count index bits inside
  have headers (offset : Nat) (atHeader : offset ∈ ([16,40,48] : List Nat)) :=
    hashInsert_header_separation_width table keys stride capacity used values order orderPos count keyLength
      arrays.keysAligned arrays.strideAligned arrays.valuesAligned arrays.usedAligned arrays.orderAligned arrays.orderPosAligned
      arrays.headerKeys arrays.headerValues arrays.keysBefore arrays.valuesBefore arrays.usedBefore arrays.orderBefore arrays.endBound
      arrays.fits arrays.room offset (by simp at atHeader; omega) (by simp at atHeader; omega)
  have headerFrame (offset : Nat) (atHeader : offset ∈ ([16,40,48] : List Nat)) :=
    sourceWriteByte_memory_other state (used + index) 0 cell (table + BitVec.ofNat 64 offset)
      ((headers offset atHeader).2.1 index inside).2.1
  apply entries.erase_slot state _ table capacity used values index targets arrays.cell16 arrays.cell48 arrays.cell40
    ((headerFrame 16 (by simp)).trans arrays.cell16) ((headerFrame 48 (by simp)).trans arrays.cell48) ((headerFrame 40 (by simp)).trans arrays.cell40)
  · have erased := sourceWriteByte_load_self state (used + index) 0 cell domain
    exact erased
  · intro slot bound different
    exact sourceWriteByte_load_other state (used + index) 0 cell (used + slot) (by simpa using different) cellMemory
  · intro slot bound _
    exact sourceWriteByte_memory_other state (used + index) 0 cell _ (byteValues slot bound)

#print axioms HashTableValuesIn.clear_occupancy
end InitECandidate.Runtime
