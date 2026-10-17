import InitECandidate.Runtime.HashDeleteCountTailLinked
import InitECandidate.Runtime.HashDeleteClearLinked32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete original post-scan suffix clears the hole and returns with
live order linkage under the decremented count. -/
theorem evaluate_hashDelete_final_tail_metadata32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos items hole deletedPosition lastSlot cell : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos items bits state)
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
      post.clock = state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have facts := invariant.insertion_memory state table keys stride capacity used values order orderPos items bits
  obtain ⟨clearRun,empty⟩ := evaluate_hashDelete_clear state used hole cell usedLocal holeLocal (facts.byteDomain hole holeInside) cellMemory
  let cleared := sourceWriteByte state (used + hole) 0 cell
  obtain ⟨reverseClear,forwardClear,headerClear⟩ := invariant.delete_clear_order_separation state table keys stride capacity used values order orderPos items hole bits holeInside
  obtain ⟨occupancy,reverse,forward,newForward,header⟩ := invariant.delete_final_separation state table keys stride capacity used values order orderPos items deletedPosition lastSlot bits deletedBound lastInside
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
  obtain ⟨post,tail,ticks,globals,code,domain,endian,_,_⟩ := evaluate_hashDelete_count_tail cleared
    table order orderPos deletedPosition items lastSlot tableLocal orderLocal reverseLocal deletedLocal
    facts.countDomain countAfter (orderDomain _ lastBound) lastAfter (orderDomain _ deletedBound) (facts.orderPosDomain lastSlot lastInside)
  refine ⟨post,?_,ticks,globals,code,domain,endian⟩
  rw [source_hashDelete_final_tail,evaluateHOLFiniteState_seq_line780,clearRun]
  exact tail

#print axioms evaluate_hashDelete_final_tail_metadata32
end InitECandidate.Runtime
