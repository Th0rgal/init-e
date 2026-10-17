import InitECandidate.Runtime.HashDeleteClearEntries
import InitECandidate.Runtime.HashDeleteOrderLinked
import InitECandidate.Runtime.HashOrderLinked
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Clearing the final hole restores linkage for every remaining occupied slot.
The old count bound is retained until the final order swap and count decrement. -/
theorem HashDeleteOrderLinked.clear {F : Type} (state : PanSemStateFiniteExact 64 F)
    (used order orderPos capacity items hole deletedPosition cell : BitVec 64)
    (linked : HashDeleteOrderLinked used order orderPos capacity items hole deletedPosition state)
    (domain : state.memaddrs (panByteAlignHOL (used + hole)))
    (memory : state.memory (panByteAlignHOL (used + hole)) = .word cell)
    (reverseSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      orderPos + slot * 8 ≠ panByteAlignHOL (used + hole))
    (forwardSeparate : ∀ position : BitVec 64, position.toNat < items.toNat →
      order + position * 8 ≠ panByteAlignHOL (used + hole)) :
    HashOrderLinked used order orderPos capacity items (sourceWriteByte state (used + hole) 0 cell) := by
  intro slot inside occupied
  have different : slot ≠ hole := by
    intro same
    subst slot
    exact occupied (sourceWriteByte_load_self state (used + hole) 0 cell domain)
  have before := sourceWriteByte_clear_occupied_before state used hole cell slot domain memory occupied
  obtain ⟨position,bound,_,reverse,forward⟩ := linked slot inside different before
  exact ⟨position,bound,
    (sourceWriteByte_memory_other state (used + hole) 0 cell (orderPos + slot * 8) (reverseSeparate slot inside)).trans reverse,
    (sourceWriteByte_memory_other state (used + hole) 0 cell (order + position * 8) (forwardSeparate position bound)).trans forward⟩

#print axioms HashDeleteOrderLinked.clear
end InitECandidate.Runtime
