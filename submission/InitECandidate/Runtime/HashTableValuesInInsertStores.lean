import InitECandidate.Runtime.HashTableValuesInStores
import InitECandidate.Runtime.HashTableValuesInExisting
import InitECandidate.Runtime.HashValueInsertGeometryWidth
import InitECandidate.Runtime.HashInsertHeaderSeparationWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The five actual insertion stores retain registered values. Marking the
new slot is allowed only after its registered value has been written. -/
theorem HashTableValuesIn.insert_value_stores {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count index cell value : BitVec 64) (bits : Nat)
    (arrays : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state)
    (member : value ∈ targets) (inside : index.toNat < capacity.toNat)
    (cellMemory : state.memory (panByteAlignHOL (used + index)) = .word cell) :
    HashTableValuesIn table targets
      (sourceWriteWord (sourceWriteWord (sourceWriteWord
        (sourceWriteByte (sourceWriteWord state (values + index * 8) value) (used + index) 1 cell)
        (order + count * 8) index) (orderPos + index * 8) count) (table + 24) (count + 1)) := by
  let written := sourceWriteWord state (values + index * 8) value
  let marked := sourceWriteByte written (used + index) 1 cell
  let ordered := sourceWriteWord marked (order + count * 8) index
  let reversed := sourceWriteWord ordered (orderPos + index * 8) count
  have facts := arrays.insertion_memory state keyLength table keys stride capacity used values order orderPos count bits
  obtain ⟨_,byteValues,bookkeepingValues⟩ := arrays.insert_value_separation_width state keyLength table keys stride capacity used values order orderPos count index bits inside
  have headers (offset : Nat) (atHeader : offset ∈ ([16,40,48] : List Nat)) :=
    hashInsert_header_separation_width table keys stride capacity used values order orderPos count keyLength
      arrays.keysAligned arrays.strideAligned arrays.valuesAligned arrays.usedAligned arrays.orderAligned arrays.orderPosAligned
      arrays.headerKeys arrays.headerValues arrays.keysBefore arrays.valuesBefore arrays.usedBefore arrays.orderBefore arrays.endBound
      arrays.fits arrays.room offset (by simp at atHeader; omega) (by simp at atHeader; omega)
  have headerFrame (offset : Nat) (atHeader : offset ∈ ([16,40,48] : List Nat)) :
      written.memory (table + BitVec.ofNat 64 offset) = state.memory (table + BitVec.ofNat 64 offset) ∧
      marked.memory (table + BitVec.ofNat 64 offset) = state.memory (table + BitVec.ofNat 64 offset) ∧
      ordered.memory (table + BitVec.ofNat 64 offset) = state.memory (table + BitVec.ofNat 64 offset) ∧
      reversed.memory (table + BitVec.ofNat 64 offset) = state.memory (table + BitVec.ofNat 64 offset) := by
    have separation := headers offset atHeader
    have wordFrame : written.memory (table + BitVec.ofNat 64 offset) = state.memory (table + BitVec.ofNat 64 offset) := by
      change (if table + BitVec.ofNat 64 offset = values + index * 8 then HolWordLab.word value else _) = _
      rw [if_neg (separation.2.1 index inside).1]
    have byteFrame : marked.memory (table + BitVec.ofNat 64 offset) = state.memory (table + BitVec.ofNat 64 offset) :=
      (sourceWriteByte_memory_other written (used + index) 1 cell _ (separation.2.1 index inside).2.1).trans wordFrame
    have orderFrame : ordered.memory (table + BitVec.ofNat 64 offset) = state.memory (table + BitVec.ofNat 64 offset) := by
      change (if table + BitVec.ofNat 64 offset = order + count * 8 then HolWordLab.word index else _) = _
      rw [if_neg separation.2.2.1]; exact byteFrame
    have reverseFrame : reversed.memory (table + BitVec.ofNat 64 offset) = state.memory (table + BitVec.ofNat 64 offset) := by
      change (if table + BitVec.ofNat 64 offset = orderPos + index * 8 then HolWordLab.word count else _) = _
      rw [if_neg (separation.2.1 index inside).2.2]; exact orderFrame
    exact ⟨wordFrame,byteFrame,orderFrame,reverseFrame⟩
  have writtenEntries := entries.write_value_layout state keyLength table keys stride capacity used values order orderPos count index value bits arrays targets member inside
  have byteAfter : written.memory (panByteAlignHOL (used + index)) = .word cell := by
    have separate : panByteAlignHOL (used + index) ≠ values + index * 8#64 := facts.valueSeparate index inside index inside
    simpa [written,sourceWriteWord,separate] using cellMemory
  have markedEntries := writtenEntries.mark_occupied written table capacity used values index cell value targets member inside
    ((headerFrame 16 (by simp)).1.trans arrays.cell16) ((headerFrame 48 (by simp)).1.trans arrays.cell48) ((headerFrame 40 (by simp)).1.trans arrays.cell40)
    byteAfter (by simp [written,sourceWriteWord]) (fun offset atHeader => (headers offset atHeader).2.1 index inside |>.2.1) byteValues
  have orderedEntries := markedEntries.after_word_separate marked table capacity used values (order + count * 8) index targets
    ((headerFrame 16 (by simp)).2.1.trans arrays.cell16) ((headerFrame 48 (by simp)).2.1.trans arrays.cell48) ((headerFrame 40 (by simp)).2.1.trans arrays.cell40)
    (fun offset atHeader => (headers offset atHeader).2.2.1)
    (fun slot bound => (facts.separate index inside slot bound).1) (fun slot bound => (bookkeepingValues slot bound).1)
  have reversedEntries := orderedEntries.after_word_separate ordered table capacity used values (orderPos + index * 8) count targets
    ((headerFrame 16 (by simp)).2.2.1.trans arrays.cell16) ((headerFrame 48 (by simp)).2.2.1.trans arrays.cell48) ((headerFrame 40 (by simp)).2.2.1.trans arrays.cell40)
    (fun offset atHeader => (headers offset atHeader).2.1 index inside |>.2.2)
    (fun slot bound => (facts.separate index inside slot bound).2.1) (fun slot bound => (bookkeepingValues slot bound).2.1)
  exact reversedEntries.after_word_separate reversed table capacity used values (table + 24) (count + 1) targets
    ((headerFrame 16 (by simp)).2.2.2.trans arrays.cell16) ((headerFrame 48 (by simp)).2.2.2.trans arrays.cell48) ((headerFrame 40 (by simp)).2.2.2.trans arrays.cell40)
    (fun offset atHeader => (headers offset atHeader).2.2.2)
    (fun slot bound => (facts.separate index inside slot bound).2.2) (fun slot bound => (bookkeepingValues slot bound).2.2)

#print axioms HashTableValuesIn.insert_value_stores
end InitECandidate.Runtime
