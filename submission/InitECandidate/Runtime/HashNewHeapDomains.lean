import InitECandidate.Runtime.HashNewFrontierFacts
import InitECandidate.Runtime.HashNewReady
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The full original heap domain supplies every constructor memory premise;
no separate assumptions about each array or aligned occupancy word are needed. -/
theorem htabNew_heap_domains {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keyLength capacity : BitVec 64) (keyBound : keyLength.toNat ≤ 52)
    (budget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address) :
    (∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabNewOrderPos table keyLength capacity).toNat + capacity.toNat * 8 → state.memaddrs address) ∧
    (∀ offset : Nat, offset ≤ 64 → state.memaddrs (table + BitVec.ofNat 64 offset)) ∧
    (∀ offset : Nat, offset < capacity.toNat → state.memaddrs (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset)) ∧
    (∀ offset : Nat, offset < capacity.toNat → state.memaddrs (panByteAlignHOL (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))) := by
  obtain ⟨_,usedAligned,_,_,_,_,usedBefore,orderBefore,endBound⟩ := htabNew_insertion_layout table keyLength capacity keyBound budget
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

#print axioms htabNew_heap_domains
end InitECandidate.Runtime
