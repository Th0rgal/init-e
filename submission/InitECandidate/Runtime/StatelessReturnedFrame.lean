import InitECandidate.Runtime.StatelessBodyReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem RlpSliceInputPrefix.after_frame {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (array input length : BitVec 64) (filled : Nat)
    (valid : RlpSliceInputPrefix state array input length filled)
    (domain : post.memaddrs = state.memaddrs) (memory : post.memory = state.memory) :
    RlpSliceInputPrefix post array input length filled := by
  intro slot inside
  obtain ⟨pointer,size,entry⟩ := valid slot inside
  exact ⟨pointer,size,entry.after_frame state post array slot pointer size input length
    domain (by rw [memory]) (by rw [memory])⟩

/-- Scope restoration and caller-local binding retain the complete decoded
contract, because they preserve its memory, globals and word-cell domain. -/
theorem StatelessReturned.after_frame {F : Type}
    (state post next : PanSemStateFiniteExact 64 F) (pointer length offsets heap : BitVec 64)
    (value : ValueHOL 64) (valid : StatelessReturned state pointer length offsets heap value post)
    (memory : next.memory = post.memory) (globals : next.globals = post.globals)
    (domain : next.memaddrs = post.memaddrs) :
    StatelessReturned state pointer length offsets heap value next := by
  have slices (a p l : BitVec 64) (n : Nat) :
      RlpSliceInputPrefix next a p l n ↔ RlpSliceInputPrefix post a p l n :=
    ⟨fun h => h.after_frame next post a p l n domain.symm memory.symm,
      fun h => h.after_frame post next a p l n domain memory⟩
  simpa only [StatelessReturned,HeapFrame,slices,memory,globals,domain] using valid

#print axioms RlpSliceInputPrefix.after_frame
#print axioms StatelessReturned.after_frame
end InitECandidate.Runtime
