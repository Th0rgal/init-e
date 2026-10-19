import InitECandidate.Runtime.WitnessArrayLinked
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A linked witness array survives a memory frame covering its two record
cells and its nonempty slice array, while the heap grows. -/
theorem WitnessArrayLinked.after_memory_between {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (si first second array count input length heap nextHeap : BitVec 64) (lower : Nat)
    (valid : WitnessArrayLinked s si first second array count input length heap)
    (firstInside : lower ≤ (si + first).toNat ∧ (si + first).toNat < heap.toNat)
    (secondInside : lower ≤ (si + second).toNat ∧ (si + second).toNat < heap.toNat)
    (arrayInside : count = 0 ∨ lower ≤ array.toNat)
    (growth : heap.toNat ≤ nextHeap.toNat)
    (domain : post.memaddrs = s.memaddrs)
    (memory : ∀ address : BitVec 64, address.toNat < heap.toNat → lower ≤ address.toNat →
      post.memory address = s.memory address) :
    WitnessArrayLinked post si first second array count input length nextHeap := by
  refine ⟨?_,?_,?_,?_,?_,valid.countBound,by have := valid.arrayEnd; omega⟩
  · rw [domain]; exact valid.pointerDomain
  · rw [domain]; exact valid.countDomain
  · rw [memory _ firstInside.2 firstInside.1]; exact valid.pointerCell
  · rw [memory _ secondInside.2 secondInside.1]; exact valid.countCell
  · rcases arrayInside with zero | above
    · subst count
      intro slot inside
      change slot.toNat < 0 at inside
      omega
    · exact valid.slices.after_memory_between s post array count input length heap lower above valid.arrayEnd domain memory

#print axioms WitnessArrayLinked.after_memory_between
end InitECandidate.Runtime
