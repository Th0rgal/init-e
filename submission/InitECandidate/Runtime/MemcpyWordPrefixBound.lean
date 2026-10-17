import InitECandidate.Runtime.MemcpyWord32LoopBound
import InitECandidate.Runtime.MemcpyWord8LoopBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Both original word-copy loops terminate within a common budget, including
all memory failures; normal completion leaves fewer than eight bytes. -/
theorem evaluate_memcpy_word_prefix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index size : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (inside : index.toNat ≤ size.toNat) (small : size.toNat ≤ 33806089496)
    (budget : (size.toNat - index.toNat) / 32 + 3 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (.seq memcpyWord32Loop memcpyWord8Loop) = (result,post) ∧
      state.clock ≤ post.clock + ((size.toNat - index.toNat) / 32 + 3) ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → ∃ finalIndex : BitVec 64,
        post.locals.lookup (ofString "i") = some (.val (.word finalIndex)) ∧
        post.locals.lookup (ofString "n") = some (.val (.word size)) ∧
        finalIndex.toNat ≤ size.toNat ∧ size.toNat - finalIndex.toNat < 8) ∧
      (∀ value, result ≠ some (.returned value)) := by
  obtain ⟨result,middle,run,cost,remaining,noTimeout,done,noReturn⟩ := evaluate_memcpy_word32_loop_bounded
    state index size indexLocal sizeLocal inside small (by omega)
  cases result with
  | some stopped =>
    refine ⟨some stopped,middle,?_,by omega,remaining,noTimeout,(by intro impossible; cases impossible),noReturn⟩
    rw [evaluateHOLFiniteState_seq_line780,run]
  | none =>
    obtain ⟨nextIndex,atIndex,atSize,bounded,remainder⟩ := done rfl
    obtain ⟨result,post,tail,tailCost,tailRemaining,tailNoTimeout,tailDone,tailNoReturn⟩ := evaluate_memcpy_word8_loop_bounded
      middle nextIndex size atIndex atSize bounded small (by omega)
    refine ⟨result,post,?_,by omega,by omega,tailNoTimeout,tailDone,tailNoReturn⟩
    rw [evaluateHOLFiniteState_seq_line780,run]
    exact tail

#print axioms evaluate_memcpy_word_prefix_bounded
end InitECandidate.Runtime
