import InitECandidate.Runtime.WitnessArrayLinked
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A linked witness array survives an older-memory window frame, and its
allocation bound follows a monotone heap frontier. Only the two record cells
and the array itself must lie in the retained window. -/
theorem WitnessArrayLinked.after_memory_between {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (si first second array count input length heap finalHeap : BitVec 64) (lower : Nat)
    (linked : WitnessArrayLinked s si first second array count input length heap)
    (pointerAbove : lower ≤ (si + first).toNat)
    (pointerBefore : (si + first).toNat < heap.toNat)
    (countAbove : lower ≤ (si + second).toNat)
    (countBefore : (si + second).toNat < heap.toNat)
    (arrayAbove : lower ≤ array.toNat)
    (monotone : heap.toNat ≤ finalHeap.toNat)
    (domain : post.memaddrs = s.memaddrs)
    (memory : ∀ address : BitVec 64, lower ≤ address.toNat → address.toNat < heap.toNat →
      post.memory address = s.memory address) :
    WitnessArrayLinked post si first second array count input length finalHeap := by
  refine ⟨?_,?_,?_,?_,?_,linked.countBound,Nat.le_trans linked.arrayEnd monotone⟩
  · rw [domain]; exact linked.pointerDomain
  · rw [domain]; exact linked.countDomain
  · rw [memory _ pointerAbove pointerBefore]; exact linked.pointerCell
  · rw [memory _ countAbove countBefore]; exact linked.countCell
  · exact RlpSliceInputPrefix.after_memory_between s post array count input length heap lower
      linked.slices arrayAbove linked.arrayEnd domain (fun address hi lo => memory address lo hi)

#print axioms WitnessArrayLinked.after_memory_between
end InitECandidate.Runtime
