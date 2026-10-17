import InitECandidate.Runtime.MemcpyWord32LoopMemoryBound
import InitECandidate.Runtime.MemcpyWord8LoopMemoryBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Both original word-copy loops terminate within a common budget, including
all memory failures; normal completion leaves fewer than eight bytes. -/
theorem evaluate_memcpy_word_prefix_memory_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination source index size watched : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (srcLocal : state.locals.lookup (ofString "src") = some (.val (.word source)))
    (separate : ∀ offset : Nat, offset < size.toNat → watched ≠ destination + BitVec.ofNat 64 offset)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (inside : index.toNat ≤ size.toNat) (small : size.toNat ≤ 33806089496)
    (budget : (size.toNat - index.toNat) / 32 + 3 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (.seq memcpyWord32Loop memcpyWord8Loop) = (result,post) ∧
      state.clock ≤ post.clock + ((size.toNat - index.toNat) / 32 + 3) ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → ∃ finalIndex : BitVec 64,
        post.locals.lookup (ofString "i") = some (.val (.word finalIndex)) ∧
        post.locals.lookup (ofString "n") = some (.val (.word size)) ∧
        finalIndex.toNat ≤ size.toNat ∧ size.toNat - finalIndex.toNat < 8 ∧
        post.locals.lookup (ofString "dst") = some (.val (.word destination)) ∧
        post.locals.lookup (ofString "src") = some (.val (.word source)) ∧ post.memory watched = state.memory watched) ∧
      (∀ value, result ≠ some (.returned value)) := by
  obtain ⟨result,middle,run,cost,remaining,noTimeout,done,noReturn⟩ := evaluate_memcpy_word32_loop_memory_bounded
    state destination source index size watched dstLocal srcLocal separate indexLocal sizeLocal inside small (by omega)
  cases result with
  | some stopped =>
    refine ⟨some stopped,middle,?_,by omega,remaining,noTimeout,(by intro impossible; cases impossible),noReturn⟩
    rw [evaluateHOLFiniteState_seq_line780,run]
  | none =>
    obtain ⟨nextIndex,atIndex,atSize,bounded,remainder,atDst,atSrc,saved⟩ := done rfl
    obtain ⟨result,post,tail,tailCost,tailRemaining,tailNoTimeout,tailDone,tailNoReturn⟩ := evaluate_memcpy_word8_loop_memory_bounded
      middle destination source nextIndex size watched atDst atSrc separate atIndex atSize bounded small (by omega)
    refine ⟨result,post,?_,by omega,by omega,tailNoTimeout,?_,tailNoReturn⟩
    · rw [evaluateHOLFiniteState_seq_line780,run]
      exact tail
    · intro normal
      obtain ⟨i,atI,atN,bound,rem,dst,src,kept⟩ := tailDone normal
      exact ⟨i,atI,atN,bound,rem,dst,src,kept.trans saved⟩

#print axioms evaluate_memcpy_word_prefix_memory_bounded
end InitECandidate.Runtime
