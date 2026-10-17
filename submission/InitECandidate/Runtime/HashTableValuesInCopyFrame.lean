import InitECandidate.Runtime.HashTableValuesInMutation
import InitECandidate.Runtime.HashTableArraysCopyFrameWidth
import InitECandidate.Runtime.HashValueCopyGeometryWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A copy retains registered values when its word and aligned byte writes
protect the relevant header fields, occupancy words, and value cells. -/
theorem HashTableValuesIn.copy_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (table capacity used values destination size : BitVec 64) (targets : Set (BitVec 64))
    (entries : HashTableValuesIn table targets state)
    (capField : state.memory (table + 16) = .word capacity)
    (usedField : state.memory (table + 48) = .word used) (valuesField : state.memory (table + 40) = .word values)
    (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be)
    (frame : ∀ cell : BitVec 64,
      (∀ offset : Nat, offset < size.toNat → cell ≠ destination + BitVec.ofNat 64 offset) →
      (∀ offset : Nat, offset < size.toNat → cell ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset)) →
      post.memory cell = state.memory cell)
    (headerSeparate : ∀ headerOffset ∈ ([16,40,48] : List Nat), ∀ offset : Nat, offset < size.toNat →
      table + BitVec.ofNat 64 headerOffset ≠ destination + BitVec.ofNat 64 offset ∧
      table + BitVec.ofNat 64 headerOffset ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset))
    (occupancySeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < size.toNat →
      panByteAlignHOL (used + slot) ≠ destination + BitVec.ofNat 64 offset ∧
      panByteAlignHOL (used + slot) ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset))
    (valueSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < size.toNat →
      values + slot * 8 ≠ destination + BitVec.ofNat 64 offset ∧
      values + slot * 8 ≠ panByteAlignHOL (destination + BitVec.ofNat 64 offset)) :
    HashTableValuesIn table targets post := by
  have headerFrame (offset : Nat) (atHeader : offset ∈ ([16,40,48] : List Nat)) :=
    frame (table + BitVec.ofNat 64 offset) (fun byte inside => (headerSeparate offset atHeader byte inside).1)
      (fun byte inside => (headerSeparate offset atHeader byte inside).2)
  apply HashTableValuesIn.of_entries post table capacity used values targets
    ((headerFrame 16 (by simp)).trans capField) ((headerFrame 48 (by simp)).trans usedField) ((headerFrame 40 (by simp)).trans valuesField)
  intro slot inside occupied value cell
  have occupancyCell := frame (panByteAlignHOL (used + slot))
    (fun byte bound => (occupancySeparate slot inside byte bound).1)
    (fun byte bound => (occupancySeparate slot inside byte bound).2)
  have reads : hashOccupancyRead post used slot = hashOccupancyRead state used slot := by
    unfold hashOccupancyRead panMemLoadByteHOL
    simp only [occupancyCell,endian]
    by_cases available : post.memaddrs (panByteAlignHOL (used + slot))
    · have before : state.memaddrs (panByteAlignHOL (used + slot)) := by rw [← domain]; exact available
      simp only [if_pos available,if_pos before]
    · have before : ¬state.memaddrs (panByteAlignHOL (used + slot)) := by rw [← domain]; exact available
      simp only [if_neg available,if_neg before]
  have valueFrame := frame (values + slot * 8) (fun byte bound => (valueSeparate slot inside byte bound).1)
    (fun byte bound => (valueSeparate slot inside byte bound).2)
  exact entries capacity used values capField usedField valuesField slot inside (by rw [← reads]; exact occupied)
    value (valueFrame.symm.trans cell)

/-- Copying a key into its slot preserves registered values using the actual
ordered key/value array geometry, including aligned partial-byte stores. -/
theorem HashTableValuesIn.key_copy_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count index : BitVec 64) (bits : Nat)
    (arrays : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state)
    (inside : index.toNat < capacity.toNat)
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be)
    (frame : ∀ cell : BitVec 64,
      (∀ offset : Nat, offset < keyLength.toNat → cell ≠ keys + index * stride + BitVec.ofNat 64 offset) →
      (∀ offset : Nat, offset < keyLength.toNat → cell ≠ panByteAlignHOL (keys + index * stride + BitVec.ofNat 64 offset)) →
      post.memory cell = state.memory cell) :
    HashTableValuesIn table targets post := by
  have headers := arrays.key_copy_header_separate_width state keyLength table keys stride capacity used values order orderPos count index bits inside
  have occupancy := (arrays.delete_occupancy_separate_width state keyLength table keys stride capacity used values order orderPos count index index bits inside inside).1
  apply entries.copy_frame state post table capacity used values (keys + index * stride) keyLength targets
    arrays.cell16 arrays.cell48 arrays.cell40 domain endian frame
  · intro offset atHeader
    exact headers offset (by simp at atHeader; omega)
  · exact occupancy
  · exact arrays.delete_copy_values_separate_width state keyLength table keys stride capacity used values order orderPos count index bits inside keysBeforeValues

#print axioms HashTableValuesIn.copy_frame
#print axioms HashTableValuesIn.key_copy_frame
end InitECandidate.Runtime
