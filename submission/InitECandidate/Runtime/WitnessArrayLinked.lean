import InitECandidate.Runtime.RlpSliceInputPrefixBetween
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A witness-list pointer/count stored in the stateless-input record, with
readable bounded input slices and the complete array below the current heap. -/
structure WitnessArrayLinked {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si first second array count input length heap : BitVec 64) : Prop where
  pointerDomain : s.memaddrs (si + first)
  countDomain : s.memaddrs (si + second)
  pointerCell : s.memory (si + first) = .word array
  countCell : s.memory (si + second) = .word count
  slices : RlpSliceInputPrefix s array input length count.toNat
  countBound : count.toNat ≤ length.toNat / 4
  arrayEnd : array.toNat + count.toNat * 16 ≤ heap.toNat

theorem WitnessArrayLinked.after_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (si first second array count input length heap : BitVec 64)
    (v : WitnessArrayLinked s si first second array count input length heap)
    (domain : post.memaddrs = s.memaddrs) (memory : post.memory = s.memory) :
    WitnessArrayLinked post si first second array count input length heap := by
  refine ⟨?_,?_,?_,?_,?_,v.countBound,v.arrayEnd⟩
  · rw [domain]; exact v.pointerDomain
  · rw [domain]; exact v.countDomain
  · rw [memory]; exact v.pointerCell
  · rw [memory]; exact v.countCell
  · intro j inside
    obtain ⟨src,len,entry⟩ := v.slices j inside
    exact ⟨src,len,entry.after_frame s post array j src len input length domain (congrFun memory _) (congrFun memory _)⟩

#print axioms WitnessArrayLinked.after_frame
end InitECandidate.Runtime
