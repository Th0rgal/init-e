import InitECandidate.Runtime.SourceByteStore
import InitECandidate.Runtime.ByteCodecPreservation
import InitECandidate.Runtime.HashOccupancyUpdate
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The exact source write exposes the low byte at its target address. -/
theorem sourceWriteByte_load_self {F : Type} (state : PanSemStateFiniteExact 64 F)
    (address value cell : BitVec 64) (domain : state.memaddrs (panByteAlignHOL address)) :
    @panMemLoadByteHOL 64 _ (sourceWriteByte state address value cell).memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be address =
        some (UInt8.ofBitVec (BitVec.ofNat 8 value.toNat)) := by
  simp [panMemLoadByteHOL,sourceWriteByte,domain]
  simpa using panGetByte_panSetByte_self address cell (BitVec.ofNat 8 value.toNat) state.be

/-- Every distinct byte is preserved, including neighboring bytes sharing the
    changed aligned word. The previous cell premise comes from the store guard. -/
theorem sourceWriteByte_load_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (address value cell current : BitVec 64) (different : current ≠ address)
    (memory : state.memory (panByteAlignHOL address) = .word cell) :
    @panMemLoadByteHOL 64 _ (sourceWriteByte state address value cell).memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be current =
    @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be current := by
  by_cases aligned : panByteAlignHOL current = panByteAlignHOL address
  · have codec := panGetByte_panSetByte_other address current cell (BitVec.ofNat 8 value.toNat)
      state.be different aligned
    simp [panMemLoadByteHOL,sourceWriteByte,aligned,memory]
    simp only [BitVec.toNat_ofNat] at codec
    rw [codec]
  · exact sourceWriteByte_load_other_word state address value cell current aligned

/-- Filling an actual empty occupancy byte increments the read-based count by
exactly one; every other slot is unchanged even when it shares that word. -/
theorem sourceWriteByte_occupancy_fill {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used slot cell : BitVec 64) (inside : slot.toNat < capacity.toNat)
    (domain : state.memaddrs (panByteAlignHOL (used + slot)))
    (memory : state.memory (panByteAlignHOL (used + slot)) = .word cell)
    (empty : hashOccupancyRead state used slot = some 0) :
    hashOccupiedCount capacity (hashOccupancyRead (sourceWriteByte state (used + slot) 1 cell) used) =
      hashOccupiedCount capacity (hashOccupancyRead state used) + 1 := by
  apply hashOccupiedCount_fill capacity slot _ _ inside empty
  · have loaded := sourceWriteByte_load_self state (used + slot) 1 cell domain
    change hashOccupancyRead (sourceWriteByte state (used + slot) 1 cell) used slot = some 1 at loaded
    rw [loaded]
    decide
  · intro index different
    have addresses : used + index ≠ used + slot := by simpa using different
    exact sourceWriteByte_load_other state (used + slot) 1 cell (used + index) addresses memory

#print axioms sourceWriteByte_load_self
#print axioms sourceWriteByte_load_other
#print axioms sourceWriteByte_occupancy_fill
end InitECandidate.Runtime
