import InitECandidate.Runtime.HashTableValuesInPhysicalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A frame below order bookkeeping, except the count word, suffices for
registered values even while occupancy and the count header are inconsistent. -/
theorem HashTableValuesIn.before_order_frame {F : Type} (geometry state post : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (arrays : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits geometry)
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state)
    (capField : state.memory (table + 16) = .word capacity)
    (usedField : state.memory (table + 48) = .word used) (valuesField : state.memory (table + 40) = .word values)
    (frame : ∀ address : BitVec 64, address.toNat < order.toNat → address ≠ table + 24 →
      post.memory address = state.memory address)
    (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be) :
    HashTableValuesIn table targets post := by
  have hv := arrays.headerValues
  have hk := arrays.headerKeys
  have ku := arrays.keysBefore
  have vu := arrays.valuesBefore
  have uo := arrays.usedBefore
  have oo := arrays.orderBefore
  have limit := arrays.endBound
  have headerFrame (offset : Nat) (member : offset ∈ ([16,40,48] : List Nat)) :
      post.memory (table + BitVec.ofNat 64 offset) = state.memory (table + BitVec.ofNat 64 offset) := by
    have small : offset ≤ 48 := by simp at member; omega
    have notCount : offset ≠ 24 := by simp at member; omega
    have natural : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
    have address : (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    apply frame
    · omega
    · intro same
      have equal := congrArg BitVec.toNat same
      have countAddress : (table + (24 : BitVec 64)).toNat = table.toNat + 24 := by
        rw [BitVec.toNat_add_of_lt (by change table.toNat + 24 < 2 ^ 64; omega)]
        rfl
      rw [address,countAddress] at equal
      omega
  have countAddress : (table + (24 : BitVec 64)).toNat = table.toNat + 24 := by
    rw [BitVec.toNat_add_of_lt (by change table.toNat + 24 < 2 ^ 64; omega)]
    rfl
  have occupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      hashOccupancyRead post used slot = hashOccupancyRead state used slot := by
    intro slot inside
    have interval := hashOccupancy_aligned_interval used capacity slot arrays.usedAligned (by omega) inside
    have cell := frame (panByteAlignHOL (used + slot)) (by omega) (by intro same; have equal := congrArg BitVec.toNat same; rw [countAddress] at equal; omega)
    unfold hashOccupancyRead panMemLoadByteHOL
    simp only [cell,endian]
    by_cases available : post.memaddrs (panByteAlignHOL (used + slot))
    · have before : state.memaddrs (panByteAlignHOL (used + slot)) := by rw [← domain]; exact available
      simp only [if_pos available,if_pos before]
    · have before : ¬state.memaddrs (panByteAlignHOL (used + slot)) := by rw [← domain]; exact available
      simp only [if_neg available,if_neg before]
  apply HashTableValuesIn.of_entries post table capacity used values targets
    ((headerFrame 16 (by simp)).trans capField) ((headerFrame 48 (by simp)).trans usedField)
    ((headerFrame 40 (by simp)).trans valuesField)
  intro slot inside occupied value cell
  have address := (hashFind_slot_address values slot 8 capacity inside
    (by change values.toNat + capacity.toNat * 8 ≤ 33806089496; omega) arrays.valuesAligned (by decide)).1
  change (values + slot * 8).toNat = values.toNat + slot.toNat * 8 at address
  have product := Nat.mul_lt_mul_of_pos_right inside (by decide : 0 < 8)
  have valueFrame := frame (values + slot * 8) (by omega) (by intro same; have equal := congrArg BitVec.toNat same; rw [countAddress] at equal; omega)
  exact entries capacity used values capField usedField valuesField slot inside
    (by rw [← occupancy slot inside]; exact occupied) value (valueFrame.symm.trans cell)

#print axioms HashTableValuesIn.before_order_frame
end InitECandidate.Runtime
