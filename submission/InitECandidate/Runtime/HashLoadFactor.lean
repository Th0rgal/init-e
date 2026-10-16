import InitECandidate.Runtime.HashProbeRank
namespace InitECandidate.Runtime

/-- The source growth guard doubles count+1. Explicit bounds prevent a
wrapped word calculation from masquerading as a valid load-factor check. -/
theorem hashGrowthGuard_toNat (count : BitVec 64) (small : count.toNat + 1 < 2 ^ 63) :
    ((count + 1) * 2).toNat = (count.toNat + 1) * 2 := by
  have addBound : count.toNat + (1 : BitVec 64).toNat < 2 ^ 64 := by
    change count.toNat + 1 < 2 ^ 64
    omega
  have added := BitVec.toNat_add_of_lt addBound
  have mulBound : (count + 1).toNat * (2 : BitVec 64).toNat < 2 ^ 64 := by
    rw [added]
    change (count.toNat + 1) * 2 < 2 ^ 64
    omega
  rw [BitVec.toNat_mul_of_lt mulBound,added]
  rfl

/-- If the actual word guard skips growth, a successful new insertion still
leaves at least one empty slot, provided its arithmetic is representable. -/
theorem hash_noGrowth_preserves_room (count capacity : BitVec 64)
    (small : count.toNat + 1 < 2 ^ 63) (skipGrowth : (count + 1) * 2 ≤ capacity) :
    count.toNat + 1 < capacity.toNat := by
  have bound := BitVec.le_def.mp skipGrowth
  rw [hashGrowthGuard_toNat count small] at bound
  omega

/-- Doubling a representable power-of-two capacity keeps the probe mask valid. -/
theorem hash_grow_capacity_power (capacity : BitVec 64) (bits : Nat)
    (power : capacity.toNat = 2 ^ bits) (small : capacity.toNat < 2 ^ 63) :
    (capacity * 2).toNat = 2 ^ (bits + 1) := by
  have mulBound : capacity.toNat * (2 : BitVec 64).toNat < 2 ^ 64 := by
    change capacity.toNat * 2 < 2 ^ 64
    omega
  rw [BitVec.toNat_mul_of_lt mulBound,power,Nat.pow_succ]
  rfl

/-- Rehashing preserves item count; doubling leaves room for the next item
when the old table was not full and its capacity was at least two. -/
theorem hash_grow_preserves_room (count capacity : Nat)
    (room : count < capacity) (nontrivial : 2 ≤ capacity) : count + 1 < capacity * 2 := by omega

#print axioms hashGrowthGuard_toNat
#print axioms hash_noGrowth_preserves_room
#print axioms hash_grow_capacity_power
#print axioms hash_grow_preserves_room
end InitECandidate.Runtime
