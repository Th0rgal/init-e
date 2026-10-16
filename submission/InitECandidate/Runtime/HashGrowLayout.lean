import InitECandidate.Runtime.HashGrowAllocationPlan
namespace InitECandidate.Runtime
open Flapjack

def htabGrowValues (pointer capacity stride : BitVec 64) : BitVec 64 :=
  allocationEnd pointer ((capacity * 2) * stride)
def htabGrowUsed (pointer capacity stride : BitVec 64) : BitVec 64 :=
  allocationEnd (htabGrowValues pointer capacity stride) ((capacity * 2) * 8)
def htabGrowOrder (pointer capacity stride : BitVec 64) : BitVec 64 :=
  allocationEnd (htabGrowUsed pointer capacity stride) (capacity * 2)
def htabGrowOrderPos (pointer capacity stride : BitVec 64) : BitVec 64 :=
  allocationEnd (htabGrowOrder pointer capacity stride) ((capacity * 2) * 8)

/-- The five original growth allocations establish all relocated-array
ordering, alignment and heap bounds needed by the insertion invariant. -/
theorem htabGrow_array_layout (table pointer capacity stride : BitVec 64)
    (strideBound : stride.toNat ≤ 56) (pointerAligned : pointer.toNat % 8 = 0)
    (headerBefore : table.toNat + 72 ≤ pointer.toNat)
    (budget : pointer.toNat + 162 * capacity.toNat + 35 ≤ 33806089496) :
    let nextCapacity := capacity * 2
    let values := htabGrowValues pointer capacity stride
    let used := htabGrowUsed pointer capacity stride
    let order := htabGrowOrder pointer capacity stride
    let orderPos := htabGrowOrderPos pointer capacity stride
    pointer.toNat % 8 = 0 ∧ values.toNat % 8 = 0 ∧ used.toNat % 8 = 0 ∧
      order.toNat % 8 = 0 ∧ orderPos.toNat % 8 = 0 ∧
      table.toNat + 72 ≤ pointer.toNat ∧ table.toNat + 72 ≤ values.toNat ∧
      pointer.toNat + nextCapacity.toNat * stride.toNat ≤ used.toNat ∧
      values.toNat + nextCapacity.toNat * 8 ≤ used.toNat ∧
      used.toNat + nextCapacity.toNat ≤ order.toNat ∧
      order.toNat + nextCapacity.toNat * 8 ≤ orderPos.toNat ∧
      orderPos.toNat + nextCapacity.toNat * 8 ≤ 33806089496 := by
  obtain ⟨doubled,safe,_⟩ := htabGrow_allocation_plan_safe pointer capacity stride strideBound budget
  obtain ⟨g1,b1,g2,b2,g3,b3,g4,b4,g5,b5,last⟩ := safe
  have c1 := allocationEnd_covers pointer ((capacity * 2) * stride)
    (allocationGuard_sum_bound _ _ (by omega) g1)
  have c2 := allocationEnd_covers (htabGrowValues pointer capacity stride) ((capacity * 2) * 8)
    (allocationGuard_sum_bound _ _ b1 g2)
  have c3 := allocationEnd_covers (htabGrowUsed pointer capacity stride) (capacity * 2)
    (allocationGuard_sum_bound _ _ b2 g3)
  have c4 := allocationEnd_covers (htabGrowOrder pointer capacity stride) ((capacity * 2) * 8)
    (allocationGuard_sum_bound _ _ b3 g4)
  have c5 := allocationEnd_covers (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)
    (allocationGuard_sum_bound _ _ b4 g5)
  have keyBound := Nat.mul_le_mul_left (2 * capacity.toNat) strideBound
  have keys : ((capacity * 2) * stride).toNat = (capacity * 2).toNat * stride.toNat :=
    BitVec.toNat_mul_of_lt (by rw [doubled]; omega)
  have words : ((capacity * 2) * (8 : BitVec 64)).toNat = (capacity * 2).toNat * 8 := by
    apply BitVec.toNat_mul_of_lt
    rw [doubled]
    change 2 * capacity.toNat * 8 < 2 ^ 64
    omega
  have lowerValues : pointer.toNat + (capacity * 2).toNat * stride.toNat ≤ (htabGrowValues pointer capacity stride).toNat := by
    simpa only [htabGrowValues,keys] using c1.1
  have lowerUsed : (htabGrowValues pointer capacity stride).toNat + (capacity * 2).toNat * 8 ≤
      (htabGrowUsed pointer capacity stride).toNat := by simpa only [htabGrowUsed,words] using c2.1
  have lowerOrder := c3.1
  have lowerReverse : (htabGrowOrder pointer capacity stride).toNat + (capacity * 2).toNat * 8 ≤
      (htabGrowOrderPos pointer capacity stride).toNat := by simpa only [htabGrowOrderPos,words] using c4.1
  have lowerEnd := c5.1
  rw [words] at lowerEnd
  change (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)).toNat ≤ 33806089496 at b5
  dsimp only
  exact ⟨pointerAligned,c1.2.2,c2.2.2,c3.2.2,c4.2.2,headerBefore,by omega,by omega,lowerUsed,lowerOrder,lowerReverse,by omega⟩

#print axioms htabGrow_array_layout
end InitECandidate.Runtime
