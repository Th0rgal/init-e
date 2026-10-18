import InitECandidate.Runtime.StatelessReturnedFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Decoded slices survive a caller allocation: memory and domains remain
fixed, while the heap/global frame may advance to another capped frontier. -/
theorem StatelessReturned.after_memory_frame {F : Type}
    (state post next : PanSemStateFiniteExact 64 F) (pointer length offsets heap : BitVec 64)
    (value : ValueHOL 64) (valid : StatelessReturned state pointer length offsets heap value post)
    (memory : next.memory = post.memory) (domain : next.memaddrs = post.memaddrs)
    (globals : HeapFrame state next) :
    StatelessReturned state pointer length offsets heap value next := by
  have slices (a p l : BitVec 64) (n : Nat) :
      RlpSliceInputPrefix next a p l n ↔ RlpSliceInputPrefix post a p l n :=
    ⟨fun h => h.after_frame next post a p l n domain.symm memory.symm,
      fun h => h.after_frame post next a p l n domain memory⟩
  refine ⟨valid.1,globals,domain.trans valid.2.2.1,?_⟩
  simpa only [slices,memory] using valid.2.2.2

#print axioms StatelessReturned.after_memory_frame
end InitECandidate.Runtime
