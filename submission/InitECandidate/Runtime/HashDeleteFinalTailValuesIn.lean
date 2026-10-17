import InitECandidate.Runtime.HashTableValuesInBeforeOrderFrame
import InitECandidate.Runtime.HashTableValuesInErase
import InitECandidate.Runtime.HashDeleteCountTailLinked
import InitECandidate.Runtime.HashDeleteClearLinkedWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete original post-scan suffix clears the hole and returns with
live order linkage under the decremented count. -/
theorem evaluate_hashDelete_final_tail_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos items hole deletedPosition lastSlot cell : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn table targets state)
    (holeInside : hole.toNat < capacity.toNat) (lastInside : lastSlot.toNat < capacity.toNat)
    (positive : 0 < items.toNat) (deletedBound : deletedPosition.toNat < items.toNat)
    (cellMemory : state.memory (panByteAlignHOL (used + hole)) = .word cell)
    (lastCell : state.memory (order + (items - 1) * 8) = .word lastSlot)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (deletedLocal : state.locals.lookup (ofString "deleted_pos") = some (.val (.word deletedPosition)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole))) :
    ∃ post, evaluateHOLFiniteState state hashDeleteFinalTail = (some (.returned (.val (.word (1 : BitVec 64)))),post) ∧
      HashTableValuesIn table targets post ∧
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
  have hv := invariant.headerValues
  have vu := invariant.valuesBefore
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
  obtain ⟨post,tail,ticks,globals,code,domain,endian,_,frame⟩ := evaluate_hashDelete_count_tail cleared
    table order orderPos deletedPosition items lastSlot tableLocal orderLocal reverseLocal deletedLocal
    facts.countDomain countAfter (orderDomain _ lastBound) lastAfter (orderDomain _ deletedBound) (facts.orderPosDomain lastSlot lastInside)
  have clearedRegistered := registered.clear_occupancy state keyLength table keys stride capacity used values order orderPos items hole cell bits invariant targets holeInside cellMemory (facts.byteDomain hole holeInside)
  have headerFrame (offset : Nat) (belongs : offset ∈ ([16,40,48] : List Nat)) :
      cleared.memory (table + BitVec.ofNat 64 offset) = state.memory (table + BitVec.ofNat 64 offset) := by
    have separate := hashInsert_header_separation_width table keys stride capacity used values order orderPos items keyLength
      invariant.keysAligned invariant.strideAligned invariant.valuesAligned invariant.usedAligned invariant.orderAligned invariant.orderPosAligned
      invariant.headerKeys invariant.headerValues invariant.keysBefore invariant.valuesBefore invariant.usedBefore invariant.orderBefore invariant.endBound
      invariant.fits invariant.room offset (by simp at belongs; omega) (by simp at belongs; omega)
    exact sourceWriteByte_memory_other state (used + hole) 0 cell _ ((separate.2.1 hole holeInside).2.1)
  have orderAddress := (hashFind_slot_address order deletedPosition 8 capacity (by omega)
    (by change order.toNat + capacity.toNat * 8 ≤ 33806089496; omega) invariant.orderAligned (by decide)).1
  have reverseAddress := (hashFind_slot_address orderPos lastSlot 8 capacity lastInside
    (by change orderPos.toNat + capacity.toNat * 8 ≤ 33806089496; exact bounded) invariant.orderPosAligned (by decide)).1
  change (order + deletedPosition * 8).toNat = order.toNat + deletedPosition.toNat * 8 at orderAddress
  change (orderPos + lastSlot * 8).toNat = orderPos.toNat + lastSlot.toNat * 8 at reverseAddress
  have postRegistered := clearedRegistered.before_order_frame state cleared post keyLength table keys stride capacity used values order orderPos items bits invariant targets
    ((headerFrame 16 (by simp)).trans invariant.cell16) ((headerFrame 48 (by simp)).trans invariant.cell48) ((headerFrame 40 (by simp)).trans invariant.cell40)
    (by
      intro address before notCount
      apply frame address
      · intro same; have equal := congrArg BitVec.toNat same; rw [orderAddress] at equal; omega
      · intro same; have equal := congrArg BitVec.toNat same; rw [reverseAddress] at equal; omega
      · exact notCount) domain endian
  refine ⟨post,?_,postRegistered,ticks,globals,code,domain,endian⟩
  rw [source_hashDelete_final_tail,evaluateHOLFiniteState_seq_line780,clearRun]
  exact tail

#print axioms evaluate_hashDelete_final_tail_values_in
end InitECandidate.Runtime
