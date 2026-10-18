import InitECandidate.Runtime.MemeqWordLoopsBound
import InitECandidate.Runtime.MemeqWord8BoundCap
import InitECandidate.Runtime.MemeqWord32BoundCap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The two original aligned word loops together use at most2n source ticks. -/
theorem evaluate_memeq_word_loops_bounded_cap {F : Type} (state : PanSemStateFiniteExact 64 F)
    (size index : BitVec 64)
    (initial : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (nLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (bounded : index.toNat ≤ size.toNat) (small : size.toNat ≤ 33806089496) (ticks : 2 * size.toNat ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state memeqWordLoops = (result,post) ∧
      state.clock ≤ post.clock + 2 * size.toNat ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → MemeqByteInvariant size post) := by
  obtain ⟨result,middle,run,cost,remaining,noTimeout,completed⟩ :=
    evaluate_memeq_word32_bounded_cap state size index initial nLocal bounded small (by omega)
  unfold memeqWordLoops
  rw [evaluateHOLFiniteState_seq_line780,run]
  cases result with
  | none =>
    obtain ⟨⟨⟨nextIndex,nextLocal,nextBound⟩,nextN⟩,_⟩ := completed rfl
    obtain ⟨tailResult,post,tail,tailCost,tailRemaining,tailNoTimeout,tailCompleted⟩ :=
      evaluate_memeq_word8_bounded_cap middle size nextIndex nextLocal nextN nextBound small (by omega)
    exact ⟨tailResult,post,tail,by omega,by omega,tailNoTimeout,(fun normal => (tailCompleted normal).1)⟩
  | some result => exact ⟨_,_,rfl,by omega,remaining,noTimeout,(by intro impossible; cases impossible)⟩

#print axioms evaluate_memeq_word_loops_bounded_cap
end InitECandidate.Runtime
