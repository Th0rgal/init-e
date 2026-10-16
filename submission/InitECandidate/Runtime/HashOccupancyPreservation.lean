import InitECandidate.Runtime.HashProbeCapacity
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Occupancy counts depend only on in-range slot reads. -/
theorem hashOccupiedCount_congr (capacity : BitVec 64) (before after : BitVec 64 → Option UInt8)
    (same : ∀ index : BitVec 64, index.toNat < capacity.toNat → before index = after index) :
    hashOccupiedCount capacity before = hashOccupiedCount capacity after := by
  unfold hashOccupiedCount
  apply List.countP_congr
  intro index member
  have bound := List.mem_range.mp member
  have wordBound : index < 2 ^ 64 := Nat.lt_trans bound capacity.isLt
  rw [same (BitVec.ofNat 64 index) (by simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt wordBound] using bound)]

/-- A bookkeeping word outside the aligned occupancy array cannot change its
byte-based count. The separation premise is about aligned cells, not bytes. -/
theorem sourceWriteWord_occupancy_preserved {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used destination value : BitVec 64)
    (separate : ∀ index : BitVec 64, index.toNat < capacity.toNat →
      panByteAlignHOL (used + index) ≠ destination) :
    hashOccupiedCount capacity (hashOccupancyRead (sourceWriteWord state destination value) used) =
      hashOccupiedCount capacity (hashOccupancyRead state used) := by
  apply hashOccupiedCount_congr
  intro index inside
  simp [hashOccupancyRead,panMemLoadByteHOL,sourceWriteWord,separate index inside]
  rfl

#print axioms hashOccupiedCount_congr
#print axioms sourceWriteWord_occupancy_preserved
end InitECandidate.Runtime
