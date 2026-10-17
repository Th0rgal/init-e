import InitECandidate.Runtime.HashDeleteFinalSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem hashOccupiedCount_clear (capacity slot : BitVec 64)
    (before after : BitVec 64 → Option UInt8) (inside : slot.toNat < capacity.toNat)
    (occupied : before slot ≠ some 0) (cleared : after slot = some 0)
    (unchanged : ∀ index, index ≠ slot → after index = before index) :
    hashOccupiedCount capacity after + 1 = hashOccupiedCount capacity before := by
  exact (hashOccupiedCount_fill capacity slot after before inside cleared occupied
    (fun index different => (unchanged index different).symm)).symm

/-- Clearing an occupied hole removes exactly one slot, including when
neighboring occupancy bytes share its aligned machine word. -/
theorem sourceWriteByte_occupancy_clear {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used slot cell : BitVec 64) (inside : slot.toNat < capacity.toNat)
    (domain : state.memaddrs (panByteAlignHOL (used + slot)))
    (memory : state.memory (panByteAlignHOL (used + slot)) = .word cell)
    (occupied : hashOccupancyRead state used slot ≠ some 0) :
    hashOccupiedCount capacity (hashOccupancyRead (sourceWriteByte state (used + slot) 0 cell) used) + 1 =
      hashOccupiedCount capacity (hashOccupancyRead state used) := by
  apply hashOccupiedCount_clear capacity slot _ _ inside occupied
  · exact sourceWriteByte_load_self state (used + slot) 0 cell domain
  · intro index different
    have addresses : used + index ≠ used + slot := by simpa using different
    exact sourceWriteByte_load_other state (used + slot) 0 cell (used + index) addresses memory

#print axioms hashOccupiedCount_clear
#print axioms sourceWriteByte_occupancy_clear
end InitECandidate.Runtime
