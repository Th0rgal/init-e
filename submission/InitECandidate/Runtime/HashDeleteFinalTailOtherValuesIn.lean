import InitECandidate.Runtime.HashDeleteFinalTailMetadataWidth
import InitECandidate.Runtime.HashDeleteCountTailOtherValuesIn
import InitECandidate.Runtime.HashTableReadyByteOutside
import InitECandidate.Runtime.HashTableValuesInArrayByteOutside
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original post-scan deletion suffix preserves disjoint ready tables. -/
theorem evaluate_hashDelete_final_tail_other_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos items hole deletedPosition lastSlot cell : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (holeInside : hole.toNat < capacity.toNat) (lastInside : lastSlot.toNat < capacity.toNat)
    (positive : 0 < items.toNat) (deletedBound : deletedPosition.toNat < items.toNat)
    (cellMemory : state.memory (panByteAlignHOL (used + hole)) = .word cell)
    (lastCell : state.memory (order + (items - 1) * 8) = .word lastSlot)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (deletedLocal : state.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (otherKeyLength otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (ready : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn otherTable targets state)
    (usedSeparate : ∀ address : BitVec 64, used.toNat ≤ address.toNat → address.toNat < used.toNat + capacity.toNat →
      ¬tablePhysicalRegion otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address)
    (orderSeparate : ∀ address : BitVec 64, order.toNat ≤ address.toNat → address.toNat < order.toNat + capacity.toNat * 8 →
      ¬tablePhysicalRegion otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address)
    (reverseSeparate : ∀ address : BitVec 64, orderPos.toNat ≤ address.toNat → address.toNat < orderPos.toNat + capacity.toNat * 8 →
      ¬tablePhysicalRegion otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos address)
    (countOutside : ¬tablePhysicalRegion otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos (table + 24)) :
    ∃ post, evaluateHOLFiniteState state hashDeleteFinalTail = (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post ∧
      HashTableValuesIn otherTable targets post ∧
      post.clock = state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have facts := invariant.insertion_memory state keyLength table keys stride capacity used values order orderPos items bits
  obtain ⟨clearRun,empty⟩ := evaluate_hashDelete_clear state used hole cell usedLocal holeLocal (facts.byteDomain hole holeInside) cellMemory
  let cleared := sourceWriteByte state (used + hole) 0 cell
  obtain ⟨reverseClear,forwardClear,headerClear⟩ := invariant.delete_clear_order_separation_width state keyLength table keys stride capacity used values order orderPos items hole bits holeInside
  obtain ⟨occupancy,reverse,forward,newForward,header⟩ := invariant.delete_final_separation_width state keyLength table keys stride capacity used values order orderPos items deletedPosition lastSlot bits deletedBound lastInside
  have subtraction : (items - (1 : BitVec 64)).toNat = items.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1 ≤ items.toNat; omega))]
    rfl
  have lastBound : (items - 1).toNat < items.toNat := by omega
  have hk := invariant.headerKeys
  have ku := invariant.keysBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have room := invariant.room
  have orderDomain : ∀ position : BitVec 64, position.toNat < items.toNat → state.memaddrs (order + position * 8) := by
    intro position inside
    have capInside : position.toNat < capacity.toNat := by omega
    have address := (hashFind_slot_address order position 8 capacity capInside
      (by change order.toNat + capacity.toNat * 8 ≤ 33806089496; omega) invariant.orderAligned (by decide)).1
    change (order + position * 8).toNat = order.toNat + position.toNat * 8 at address
    have product := Nat.mul_lt_mul_of_pos_right capInside (by decide : 0 < 8)
    apply invariant.domain <;> omega
  have countAfter : cleared.memory (table + 24) = .word items :=
    (sourceWriteByte_memory_other state (used + hole) 0 cell (table + 24) headerClear).trans invariant.cell24
  have lastAfter : cleared.memory (order + (items - 1) * 8) = .word lastSlot :=
    (sourceWriteByte_memory_other state (used + hole) 0 cell _ (forwardClear _ lastBound)).trans lastCell
  have clearedReady := ready.after_array_byte_physical state otherKeyLength otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems used capacity hole 0 cell otherBits
    holeInside invariant.usedAligned (by omega) usedSeparate
  have clearedValues := registered.after_array_byte_outside state otherKeyLength otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems used capacity hole 0 cell otherBits ready targets
    holeInside invariant.usedAligned (by omega) usedSeparate
  obtain ⟨post,tail,otherReady,otherValuesPreserved,ticks,globals,code,domain,endian⟩ := evaluate_hashDelete_count_tail_other_values_in cleared
    table order orderPos deletedPosition items lastSlot tableLocal orderLocal reverseLocal deletedLocal
    facts.countDomain countAfter (orderDomain _ lastBound) lastAfter (orderDomain _ deletedBound) (facts.orderPosDomain lastSlot lastInside)
    capacity (by omega) lastInside invariant.orderAligned invariant.orderPosAligned (by omega) bounded
    otherKeyLength otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
    clearedReady targets clearedValues orderSeparate reverseSeparate countOutside
  refine ⟨post,?_,otherReady,otherValuesPreserved,ticks,globals,code,domain,endian⟩
  rw [source_hashDelete_final_tail,evaluateHOLFiniteState_seq_line780,clearRun]
  exact tail


#print axioms evaluate_hashDelete_final_tail_other_values_in
end InitECandidate.Runtime
