import InitECandidate.Runtime.HashNewHeapDomains
import InitECandidate.Runtime.HashNewSafePlanGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A full heap domain supplies constructor memory premises from the actual
safe allocation plan, without a conservative reservation requirement. -/
theorem htabNew_heap_domains_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keyLength capacity : BitVec 64) (pointerBound : table.toNat ≤ 33806089496)
    (fullSafe : AllocationPlanSafe table (htabNewAllocationSizes keyLength capacity))
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address) :
    (∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabNewOrderPos table keyLength capacity).toNat + capacity.toNat * 8 → state.memaddrs address) ∧
    (∀ offset : Nat, offset ≤ 64 → state.memaddrs (table + BitVec.ofNat 64 offset)) ∧
    (∀ offset : Nat, offset < capacity.toNat → state.memaddrs (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset)) ∧
    (∀ offset : Nat, offset < capacity.toNat → state.memaddrs (panByteAlignHOL (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))) := by
  obtain ⟨_,usedAligned,_,_,_,_,usedBefore,orderBefore,endBound⟩ := htabNew_insertion_layout_of_safe_plan table keyLength capacity pointerBound fullSafe
  have capacityBound : capacity.toNat < 2 ^ 64 := capacity.isLt
  have usedEnd : (htabNewUsed table keyLength capacity).toNat + capacity.toNat ≤ 33806089496 := by omega
  refine ⟨?_,?_,?_,?_⟩
  · intro address lower upper
    exact heapDomain address (by omega)
  · intro offset inside
    have natural : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
    have address : (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    exact heapDomain _ (by omega)
  · intro offset inside
    have natural : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
    have address : (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset).toNat = (htabNewUsed table keyLength capacity).toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    exact heapDomain _ (by omega)
  · intro offset inside
    have natural : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
    have interval := hashOccupancy_aligned_interval (htabNewUsed table keyLength capacity) capacity (BitVec.ofNat 64 offset)
      usedAligned (by omega) (by rw [natural]; exact inside)
    exact heapDomain _ (by omega)

#print axioms htabNew_heap_domains_of_safe_plan
end InitECandidate.Runtime
