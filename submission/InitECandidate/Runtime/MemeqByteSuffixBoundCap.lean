import InitECandidate.Runtime.MemeqByteSuffixBound
import InitECandidate.Runtime.MemeqByte8BoundCap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The exact original byte-comparison suffix (eight-byte loop, one-byte
loop and final return) costs at most2n source ticks for n≤cap. All early
mismatch returns and invalid reads are included. -/
theorem evaluate_memeq_byte_suffix_bounded_cap {F : Type} (state : PanSemStateFiniteExact 64 F)
    (size index : BitVec 64)
    (initial : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (nLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (bounded : index.toNat ≤ size.toNat) (small : size.toNat ≤ 33806089496) (ticks : 2 * size.toNat ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state memeqAfterAligned = (result,post) ∧
      state.clock ≤ post.clock + 2 * size.toNat ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut := by
  obtain ⟨result,middle,run,cost,remaining,noTimeout,completed⟩ :=
    evaluate_memeq_byte8_bounded_cap state size index initial nLocal bounded small (by omega)
  rw [source_memeq_byte_suffix,evaluateHOLFiniteState_seq_line780,run]
  cases result with
  | none =>
    obtain ⟨⟨⟨nextIndex,nextLocal,nextBound⟩,nextN⟩,_⟩ := completed rfl
    obtain ⟨tailResult,post,tail,tailCost,tailRemaining,tailNoTimeout,_⟩ :=
      evaluate_memeq_byte1_bounded_cap middle size nextIndex nextLocal nextN nextBound small (by omega)
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780,tail]
    cases tailResult with
    | none =>
      simp only [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
      dsimp only [emptyLocalsHOLFinite]
      exact ⟨_,_,rfl,(by change state.clock ≤ post.clock + 2 * size.toNat; omega),
        (by change post.clock ≤ state.clock; omega),by simp⟩
    | some finalResult => exact ⟨_,_,rfl,by omega,by omega,tailNoTimeout⟩
  | some result => exact ⟨_,_,rfl,by omega,remaining,noTimeout⟩

#print axioms evaluate_memeq_byte_suffix_bounded_cap
end InitECandidate.Runtime
