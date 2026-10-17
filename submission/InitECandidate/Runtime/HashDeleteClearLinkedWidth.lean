import InitECandidate.Runtime.HashDeleteClearGeometryWidth
import InitECandidate.Runtime.HashDeleteClearLinked
import InitECandidate.Runtime.HashDeleteOrderLinkedMove
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Clearing the final hole preserves deletion coherence and restores live
linkage, with all cell separation derived from the pre-clear table layout. -/
theorem HashDeleteOrderLinked.clear_layout_width {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos items hole deletedPosition cell : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (linked : HashDeleteOrderLinked used order orderPos capacity items hole deletedPosition state)
    (inside : hole.toNat < capacity.toNat)
    (memory : state.memory (panByteAlignHOL (used + hole)) = .word cell) :
    HashDeleteOrderLinked used order orderPos capacity items hole deletedPosition (sourceWriteByte state (used + hole) 0 cell) ∧
    HashOrderLinked used order orderPos capacity items (sourceWriteByte state (used + hole) 0 cell) := by
  have facts := invariant.insertion_memory state keyLength table keys stride capacity used values order orderPos items bits
  obtain ⟨reverse,forward,_⟩ := invariant.delete_clear_order_separation_width state keyLength table keys stride capacity used values order orderPos items hole bits inside
  constructor
  · apply linked.framed state _ used order orderPos capacity items hole deletedPosition
    · intro slot bound different occupied
      exact sourceWriteByte_clear_occupied_before state used hole cell slot (facts.byteDomain hole inside) memory occupied
    · intro slot bound different
      exact sourceWriteByte_memory_other state (used + hole) 0 cell (orderPos + slot * 8) (reverse slot bound)
    · intro position bound notDeleted
      exact sourceWriteByte_memory_other state (used + hole) 0 cell (order + position * 8) (forward position bound)
  · exact linked.clear state used order orderPos capacity items hole deletedPosition cell (facts.byteDomain hole inside) memory reverse forward

#print axioms HashDeleteOrderLinked.clear_layout_width
end InitECandidate.Runtime
