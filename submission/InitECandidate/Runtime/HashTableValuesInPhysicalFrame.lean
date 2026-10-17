import InitECandidate.Runtime.HashTableValuesInMutation
import InitECandidate.Runtime.HashTablePhysicalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Writes outside a table's live physical regions preserve its registered
values, even when arrays were relocated and other globals or locals change. -/
theorem HashTableValuesIn.physical_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (arrays : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state)
    (frame : ∀ address : BitVec 64, tablePhysicalRegion table keys stride capacity used values order orderPos address →
      post.memory address = state.memory address)
    (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be) :
    HashTableValuesIn table targets post := by
  have hk := arrays.headerKeys
  have ku := arrays.keysBefore
  have vu := arrays.valuesBefore
  have uo := arrays.usedBefore
  have oo := arrays.orderBefore
  have limit := arrays.endBound
  have headerFrame (offset : Nat) (small : offset ≤ 64) :
      post.memory (table + BitVec.ofNat 64 offset) = state.memory (table + BitVec.ofNat 64 offset) := by
    have natural : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
    have address : (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    apply frame
    exact Or.inl ⟨by omega,by omega⟩
  have occupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      hashOccupancyRead post used slot = hashOccupancyRead state used slot := by
    intro slot inside
    have interval := hashOccupancy_aligned_interval used capacity slot arrays.usedAligned (by omega) inside
    have cell := frame (panByteAlignHOL (used + slot)) (by unfold tablePhysicalRegion; omega)
    unfold hashOccupancyRead panMemLoadByteHOL
    simp only [cell,endian]
    by_cases available : post.memaddrs (panByteAlignHOL (used + slot))
    · have before : state.memaddrs (panByteAlignHOL (used + slot)) := by rw [← domain]; exact available
      simp only [if_pos available,if_pos before]
    · have before : ¬state.memaddrs (panByteAlignHOL (used + slot)) := by rw [← domain]; exact available
      simp only [if_neg available,if_neg before]
  apply HashTableValuesIn.of_entries post table capacity used values targets
    ((headerFrame 16 (by decide)).trans arrays.cell16) ((headerFrame 48 (by decide)).trans arrays.cell48)
    ((headerFrame 40 (by decide)).trans arrays.cell40)
  intro slot inside occupied value cell
  have address := (hashFind_slot_address values slot 8 capacity inside
    (by change values.toNat + capacity.toNat * 8 ≤ 33806089496; omega) arrays.valuesAligned (by decide)).1
  change (values + slot * 8).toNat = values.toNat + slot.toNat * 8 at address
  have product := Nat.mul_lt_mul_of_pos_right inside (by decide : 0 < 8)
  have valueFrame := frame (values + slot * 8) (by unfold tablePhysicalRegion; omega)
  exact entries capacity used values arrays.cell16 arrays.cell48 arrays.cell40 slot inside
    (by rw [← occupancy slot inside]; exact occupied) value (valueFrame.symm.trans cell)

/-- A store to another table or journal cell preserves registered pointers
when its destination is outside this table's live physical footprint. -/
theorem HashTableValuesIn.after_word_outside {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count destination value : BitVec 64) (bits : Nat)
    (arrays : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state)
    (outside : ¬tablePhysicalRegion table keys stride capacity used values order orderPos destination) :
    HashTableValuesIn table targets (sourceWriteWord state destination value) := by
  apply entries.physical_frame state _ keyLength table keys stride capacity used values order orderPos count bits arrays targets
  · intro address member
    have different : address ≠ destination := by intro same; subst address; exact outside member
    change (if address = destination then HolWordLab.word value else _) = _
    rw [if_neg different]
  · rfl
  · rfl

#print axioms HashTableValuesIn.physical_frame
#print axioms HashTableValuesIn.after_word_outside
end InitECandidate.Runtime
