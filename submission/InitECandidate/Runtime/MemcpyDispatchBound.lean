import InitECandidate.Runtime.MemcpyWordPrefixBound
import InitECandidate.Runtime.MemcpyByteSuffixBound
import InitECandidate.Runtime.MemcpyAlignedBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Both alignment paths of the original copy compose into a uniform budget;
all failed memory operations remain covered by their actual executions. -/
theorem evaluate_memcpy_after_index_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index size flag : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (inside : index.toNat ≤ size.toNat) (small : size.toNat ≤ 33806089496)
    (condition : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      memcpyAlignmentCondition = some (.val (.word flag)))
    (budget : (size.toNat - index.toNat) / 32 + (size.toNat - index.toNat) / 8 + 10 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state memcpyAfterIndex = (result,post) ∧
      state.clock ≤ post.clock + ((size.toNat - index.toNat) / 32 + (size.toNat - index.toNat) / 8 + 10) ∧
      post.clock ≤ state.clock ∧ result ≠ some .timeOut := by
  change ∃ result post, evaluateHOLFiniteState state
    (.seq (.ite memcpyAlignmentCondition (.seq memcpyWord32Loop memcpyWord8Loop) .skip) memcpyByteSuffix) = (result,post) ∧ _
  by_cases zero : flag = 0
  · have branch : evaluateHOLFiniteState state (.ite memcpyAlignmentCondition (.seq memcpyWord32Loop memcpyWord8Loop) .skip) = (none,state) := by
      rw [evaluateHOLFiniteState_ite,condition]
      simp only [if_pos zero,evaluateHOLFiniteState_skip]
    obtain ⟨result,post,run,cost,remaining,noTimeout⟩ := evaluate_memcpy_byte_suffix_bounded state index size indexLocal sizeLocal inside small (by omega)
    refine ⟨result,post,?_,by omega,remaining,noTimeout⟩
    rw [evaluateHOLFiniteState_seq_line780,branch]
    exact run
  · have branch : evaluateHOLFiniteState state (.ite memcpyAlignmentCondition (.seq memcpyWord32Loop memcpyWord8Loop) .skip) =
        evaluateHOLFiniteState state (.seq memcpyWord32Loop memcpyWord8Loop) := by
      rw [evaluateHOLFiniteState_ite,condition]
      simp only [if_neg zero]
    obtain ⟨result,middle,run,cost,remaining,noTimeout,done,_⟩ := evaluate_memcpy_word_prefix_bounded state index size indexLocal sizeLocal inside small (by omega)
    cases result with
    | some stopped =>
      refine ⟨some stopped,middle,?_,by omega,remaining,noTimeout⟩
      rw [evaluateHOLFiniteState_seq_line780,branch,run]
    | none =>
      obtain ⟨nextIndex,atIndex,atSize,bounded,remainder⟩ := done rfl
      obtain ⟨result,post,tail,tailCost,tailRemaining,tailNoTimeout⟩ := evaluate_memcpy_byte_suffix_bounded
        middle nextIndex size atIndex atSize bounded small (by omega)
      refine ⟨result,post,?_,by omega,by omega,tailNoTimeout⟩
      rw [evaluateHOLFiniteState_seq_line780,branch,run]
      exact tail

#print axioms evaluate_memcpy_after_index_bounded
end InitECandidate.Runtime
