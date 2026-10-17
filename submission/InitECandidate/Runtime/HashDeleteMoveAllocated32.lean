import InitECandidate.Runtime.HashDeleteMoveAllInvariants
import InitECandidate.Runtime.HashDeleteCopyBounds32
import InitECandidate.Runtime.HashDeleteCopyGeometry32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Table allocation supplies all key-copy domains and protected source cells. -/
theorem evaluate_hashDelete_move_allocated32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keys stride hole scan values order orderPos position value used capacity items : BitVec 64)
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (scanLocal : state.locals.lookup (ofString "j") = some (.val (.word scan)))
    (sizeLocal : state.locals.lookup (ofString "klen") = some (.val (.word (32 : BitVec 64))))
    (table : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos items bits state)
    (scanInside : scan.toNat < capacity.toNat)
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (budget : 33 ≤ state.clock)
    (valuesLocal : state.locals.lookup (ofString "vals") = some (.val (.word values)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (valueDomain : state.memaddrs (values + scan * 8))
    (valueCell : state.memory (values + scan * 8) = .word value)
    (destinationDomain : state.memaddrs (values + hole * 8))
    (loadDomain : state.memaddrs (orderPos + scan * 8))
    (loadCell : state.memory (orderPos + scan * 8) = .word position)
    (separate : orderPos + scan * 8 ≠ values + hole * 8)
    (orderDomain : state.memaddrs (order + position * 8))
    (reverseDomain : state.memaddrs (orderPos + hole * 8))
    (entries : HashReverseEntriesBound used orderPos capacity items state)
    (positionBound : position.toNat < items.toNat)
    (copyOccupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < 32 →
      panByteAlignHOL (used + slot) ≠ keys + hole * stride + BitVec.ofNat 64 offset ∧
      panByteAlignHOL (used + slot) ≠ panByteAlignHOL (keys + hole * stride + BitVec.ofNat 64 offset))
    (copyReverse : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < 32 →
      orderPos + slot * 8 ≠ keys + hole * stride + BitVec.ofNat 64 offset ∧
      orderPos + slot * 8 ≠ panByteAlignHOL (keys + hole * stride + BitVec.ofNat 64 offset))
    (valueOccupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ values + hole * 8)
    (valueReverse : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      orderPos + slot * 8 ≠ values + hole * 8)
    (storeOccupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ order + position * 8 ∧
      panByteAlignHOL (used + slot) ≠ orderPos + hole * 8)
    (storeReverse : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ hole →
      orderPos + slot * 8 ≠ order + position * 8 ∧ orderPos + slot * 8 ≠ orderPos + hole * 8)
    (orderEntries : HashOrderEntriesBound order capacity items state)
    (holeInside : hole.toNat < capacity.toNat)
    (copyOrder : ∀ index : BitVec 64, index.toNat < items.toNat → ∀ offset : Nat, offset < 32 →
      order + index * 8 ≠ keys + hole * stride + BitVec.ofNat 64 offset ∧
      order + index * 8 ≠ panByteAlignHOL (keys + hole * stride + BitVec.ofNat 64 offset))
    (valueSeparate : ∀ index : BitVec 64, index.toNat < items.toNat → order + index * 8 ≠ values + hole * 8)
    (orderSeparate : ∀ index : BitVec 64, index.toNat < items.toNat → order + index * 8 ≠ orderPos + hole * 8)
    (positionSeparate : order + position * 8 ≠ orderPos + hole * 8)
    (distinct : ∀ index : BitVec 64, index.toNat < items.toNat → index ≠ position →
      order + index * 8 ≠ order + position * 8)
    (valueEntries : HashValueEntriesWord used values capacity state)
    (copyValues : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < 32 →
      values + slot * 8 ≠ keys + hole * stride + BitVec.ofNat 64 offset ∧
      values + slot * 8 ≠ panByteAlignHOL (keys + hole * stride + BitVec.ofNat 64 offset))
    (valueDistinct : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ hole →
      values + slot * 8 ≠ values + hole * 8)
    (orderValues : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → values + slot * 8 ≠ order + position * 8)
    (reverseValues : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → values + slot * 8 ≠ orderPos + hole * 8) :
    ∃ post, evaluateHOLFiniteState state hashDeleteMoveBody = (none,post) ∧
      state.clock ≤ post.clock + 32 + 1 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ HashReverseEntriesBound used orderPos capacity items post ∧ HashOrderEntriesBound order capacity items post ∧
      (∀ slot : BitVec 64, slot.toNat < capacity.toNat →
        hashOccupancyRead post used slot = hashOccupancyRead state used slot) ∧
      post.locals = (setVarHOLFinite (ofString "i") (.val (.word scan)) state).locals ∧ HashValueEntriesWord used values capacity post := by
  have bounds := invariant.delete_copy_bounds state table keys stride capacity used values order orderPos items hole scan bits holeInside scanInside
  have protectedCells := invariant.delete_copy_separate state table keys stride capacity used values order orderPos items hole scan bits holeInside scanInside keysBeforeValues
  exact evaluate_hashDelete_move_all_invariants state keys stride hole scan 32 values order orderPos position value used capacity items
    keysLocal strideLocal holeLocal scanLocal sizeLocal bounds.small bounds.aligned bounds.sourceAligned budget
    bounds.wordDomain bounds.byteDomain bounds.sourceWordDomain bounds.sourceByteDomain protectedCells invariant.code
    valuesLocal orderLocal reverseLocal valueDomain valueCell destinationDomain loadDomain loadCell separate orderDomain reverseDomain
    entries positionBound copyOccupancy copyReverse valueOccupancy valueReverse storeOccupancy storeReverse
    orderEntries holeInside copyOrder valueSeparate orderSeparate positionSeparate distinct
    valueEntries copyValues valueDistinct orderValues reverseValues

#print axioms evaluate_hashDelete_move_allocated32
end InitECandidate.Runtime
