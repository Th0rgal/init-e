import InitECandidate.Runtime.HashDeleteMoveAllocatedWidth
import InitECandidate.Runtime.HashDeleteMovePhysical
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Allocated table geometry discharges the complete movement frame premises. -/
theorem evaluate_hashDelete_move_allocated_physical {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength keys stride hole scan values order orderPos used capacity items : BitVec 64)
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (scanLocal : state.locals.lookup (ofString "j") = some (.val (.word scan)))
    (sizeLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (table : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (scanInside : scan.toNat < capacity.toNat)
    (occupied : hashOccupancyRead state used scan ≠ some 0)
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (budget : keyLength.toNat + 1 ≤ state.clock)
    (valuesLocal : state.locals.lookup (ofString "vals") = some (.val (.word values)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (entries : HashReverseEntriesBound used orderPos capacity items state)
    (orderEntries : HashOrderEntriesBound order capacity items state)
    (holeInside : hole.toNat < capacity.toNat)
    (valueEntries : HashValueEntriesWord used values capacity state)
    (otherKeyLength otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (ready : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (separated : ∀ address : BitVec 64,
      tablePhysicalRegion table keys stride capacity used values order orderPos address →
      ¬tablePhysicalRegion otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address) :
    ∃ post, evaluateHOLFiniteState state hashDeleteMoveBody = (none,post) ∧
      HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post ∧
      state.clock ≤ post.clock + keyLength.toNat + 1 ∧ post.clock ≤ state.clock ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨value,valueCell⟩ := valueEntries scan scanInside occupied
  obtain ⟨position,loadCell,positionBound⟩ := entries scan scanInside occupied
  have bounds := invariant.delete_copy_bounds_width state keyLength table keys stride capacity used values order orderPos items hole scan bits holeInside scanInside
  have protectedCells := invariant.delete_copy_separate_width state keyLength table keys stride capacity used values order orderPos items hole scan bits holeInside scanInside keysBeforeValues
  have occupancy := invariant.delete_occupancy_separate_width state keyLength table keys stride capacity used values order orderPos items hole position bits
    holeInside (Nat.lt_trans positionBound invariant.room)
  have copyOccupancy := occupancy.1
  have valueOccupancy := fun slot inside => (occupancy.2 slot inside).1
  have storeOccupancy := fun slot inside => (occupancy.2 slot inside).2
  have valueReverse := invariant.value_reverse_separate_width state keyLength table keys stride capacity used values order orderPos items hole bits holeInside
  have copyReverse := invariant.delete_copy_reverse_separate_width state keyLength table keys stride capacity used values order orderPos items hole bits holeInside
  have copyValues := invariant.delete_copy_values_separate_width state keyLength table keys stride capacity used values order orderPos items hole bits holeInside keysBeforeValues
  obtain ⟨copyOrder,valueSeparate⟩ := invariant.delete_order_frames_width state keyLength table keys stride capacity used values order orderPos items hole bits holeInside
  have separate := valueReverse scan scanInside
  have valueDistinct := (invariant.insert_value_separation_width state keyLength table keys stride capacity used values order orderPos items hole bits holeInside).1
  have orderValues : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → values + slot * 8 ≠ order + position * 8 := by
    intro slot inside
    exact Ne.symm ((invariant.delete_order_frames_width state keyLength table keys stride capacity used values order orderPos items slot bits inside).2 position positionBound)
  have reverseValues : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → values + slot * 8 ≠ orderPos + hole * 8 := by
    intro slot inside
    exact Ne.symm (invariant.value_reverse_separate_width state keyLength table keys stride capacity used values order orderPos items slot bits inside hole holeInside)
  have storeReverse := invariant.delete_reverse_separate_width state keyLength table keys stride capacity used values order orderPos items hole position bits
    holeInside (Nat.lt_trans positionBound invariant.room)
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have room := invariant.room
  have orderAddress : ∀ index : BitVec 64, index.toNat < capacity.toNat →
      (order + index * 8).toNat = order.toNat + index.toNat * 8 := by
    intro index inside
    exact (hashFind_slot_address order index 8 capacity inside
      (by change order.toNat + capacity.toNat * 8 ≤ 33806089496; omega) invariant.orderAligned (by decide)).1
  have reverseAddress := (hashFind_slot_address orderPos hole 8 capacity holeInside
    (by change orderPos.toNat + capacity.toNat * 8 ≤ 33806089496; exact bounded) invariant.orderPosAligned (by decide)).1
  change (orderPos + hole * 8).toNat = orderPos.toNat + hole.toNat * 8 at reverseAddress
  have orderSeparate : ∀ index : BitVec 64, index.toNat < items.toNat → order + index * 8 ≠ orderPos + hole * 8 := by
    intro index inside same
    have natural := congrArg BitVec.toNat same
    rw [orderAddress index (by omega),reverseAddress] at natural
    have product := Nat.mul_lt_mul_of_pos_right (show index.toNat < capacity.toNat by omega) (by decide : 0 < 8)
    omega
  have positionSeparate := orderSeparate position positionBound
  have distinct : ∀ index : BitVec 64, index.toNat < items.toNat → index ≠ position → order + index * 8 ≠ order + position * 8 := by
    intro index inside different same
    have natural := congrArg BitVec.toNat same
    rw [orderAddress index (by omega),orderAddress position (by omega)] at natural
    exact different (BitVec.eq_of_toNat_eq (by omega))
  have facts := invariant.insertion_memory state keyLength table keys stride capacity used values order orderPos items bits
  have valueDomain := facts.valueDomain scan scanInside
  have destinationDomain := facts.valueDomain hole holeInside
  have hk := invariant.headerKeys
  have ku := invariant.keysBefore
  have uo := invariant.usedBefore
  have reverseAvailable : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → state.memaddrs (orderPos + slot * 8) := facts.orderPosDomain
  have loadDomain := reverseAvailable scan scanInside
  have reverseDomain := reverseAvailable hole holeInside
  have orderDomain : state.memaddrs (order + position * 8) := by
    have address := orderAddress position (Nat.lt_trans positionBound room)
    have product := Nat.mul_lt_mul_of_pos_right (Nat.lt_trans positionBound room) (by decide : 0 < 8)
    apply invariant.domain <;> omega
  have hv := invariant.headerValues
  have vu := invariant.valuesBefore
  have keyAddress := (hashFind_slot_address keys hole stride capacity holeInside (by omega) invariant.keysAligned invariant.strideAligned).1
  have next := Nat.mul_le_mul_right stride.toNat (show hole.toNat + 1 ≤ capacity.toNat by omega)
  rw [Nat.add_mul,Nat.one_mul] at next
  have fits := invariant.fits
  have copyOutside : ∀ address : BitVec 64,
      (keys + hole * stride).toNat ≤ address.toNat → address.toNat < (keys + hole * stride).toNat + keyLength.toNat →
      ¬tablePhysicalRegion otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address := by
    intro address lower upper
    apply separated address
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  apply evaluate_hashDelete_move_physical state keyLength keys stride hole scan values order orderPos position value used capacity items
    keysLocal strideLocal holeLocal scanLocal sizeLocal bounds.small bounds.aligned bounds.sourceAligned budget
    bounds.wordDomain bounds.byteDomain bounds.sourceWordDomain bounds.sourceByteDomain protectedCells invariant.code
    valuesLocal orderLocal reverseLocal valueDomain valueCell destinationDomain loadDomain loadCell separate orderDomain reverseDomain
    table bits invariant holeInside positionBound otherKeyLength otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits ready copyOutside
  · intro address lower upper
    exact separated address (Or.inr (Or.inr (Or.inr (Or.inl ⟨lower,upper⟩))))
  · intro address lower upper
    exact separated address (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨lower,upper⟩)))))
  · intro address lower upper
    exact separated address (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨lower,upper⟩)))))

#print axioms evaluate_hashDelete_move_allocated_physical
end InitECandidate.Runtime
