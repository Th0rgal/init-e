import InitECandidate.Runtime.HashDeleteRank
namespace InitECandidate.Runtime

/-- The current hole is no farther along the scan toward a fixed empty slot
than the scan index. This is initially reflexive and survives either move choice. -/
def HashDeleteScanOrder (capacity index hole empty : BitVec 64) : Prop :=
  hashDeleteRank capacity index empty ≤ hashDeleteRank capacity hole empty

theorem HashDeleteScanOrder.initial (capacity hole empty : BitVec 64) :
    HashDeleteScanOrder capacity hole hole empty := Nat.le_refl _

/-- An occupied scan advance cannot revisit the hole before reaching the fixed empty slot. -/
theorem HashDeleteScanOrder.next_ne_hole (capacity index hole empty : BitVec 64) (bits : Nat)
    (ordered : HashDeleteScanOrder capacity index hole empty)
    (power : capacity.toNat = 2 ^ bits) (inside : index.toNat < capacity.toNat)
    (emptyInside : empty.toNat < capacity.toNat)
    (notEmpty : hashProbeNext index capacity ≠ empty) :
    hashProbeNext index capacity ≠ hole := by
  have decreases := hashDeleteRank_decreases capacity index empty bits power inside emptyInside notEmpty
  intro same
  rw [same] at decreases
  unfold HashDeleteScanOrder at ordered
  omega

/-- Skipping an entry keeps the old hole behind the advanced index. -/
theorem HashDeleteScanOrder.advance (capacity index hole empty : BitVec 64) (bits : Nat)
    (ordered : HashDeleteScanOrder capacity index hole empty)
    (power : capacity.toNat = 2 ^ bits) (inside : index.toNat < capacity.toNat)
    (emptyInside : empty.toNat < capacity.toNat)
    (notEmpty : hashProbeNext index capacity ≠ empty) :
    HashDeleteScanOrder capacity (hashProbeNext index capacity) hole empty := by
  have decreases := hashDeleteRank_decreases capacity index empty bits power inside emptyInside notEmpty
  unfold HashDeleteScanOrder at *
  omega

/-- Moving the scanned entry sets hole and scan index to the same slot. -/
theorem HashDeleteScanOrder.move (capacity index empty : BitVec 64) :
    HashDeleteScanOrder capacity (hashProbeNext index capacity) (hashProbeNext index capacity) empty :=
  HashDeleteScanOrder.initial _ _ _

#print axioms HashDeleteScanOrder.initial
#print axioms HashDeleteScanOrder.next_ne_hole
#print axioms HashDeleteScanOrder.advance
#print axioms HashDeleteScanOrder.move
end InitECandidate.Runtime
