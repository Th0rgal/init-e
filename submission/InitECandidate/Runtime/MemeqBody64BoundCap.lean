import InitECandidate.Runtime.MemeqBody64Bound
import InitECandidate.Runtime.MemeqAlignedBoundCap
import InitECandidate.Runtime.MemeqByteSuffixBoundCap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Alignment dispatch includes malformed pointer expressions and all fixed
fast paths. Normal fallthrough retains the counter and length invariant. -/
theorem evaluate_memeq_alignment_choice_bounded_cap {F : Type} (state : PanSemStateFiniteExact 64 F)
    (size index : BitVec 64)
    (initial : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (nLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (bounded : index.toNat ≤ size.toNat) (small : size.toNat ≤ 33806089496) (ticks : 2 * size.toNat ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state memeqAlignmentChoice = (result,post) ∧
      state.clock ≤ post.clock + 2 * size.toNat ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → MemeqByteInvariant size post) := by
  unfold memeqAlignmentChoice
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · rw [evaluateHOLFiniteState_skip]
      exact ⟨none,state,rfl,by omega,by omega,by simp,(by intro _; exact ⟨⟨index,initial,bounded⟩,nLocal⟩)⟩
    · exact evaluate_memeq_aligned_bounded_cap state size index initial nLocal bounded small ticks
  · exact ⟨some .error,state,rfl,by omega,by omega,by simp,(by intro impossible; cases impossible)⟩

/-- Complete original memeq body for trie-sized lengths. The conservative
4n source-clock bound covers both alignments, fast paths, mismatches and
invalid memory, without requiring successful reads or aligned pointers. -/
theorem evaluate_memeq_body64_bounded_cap {F : Type} (state : PanSemStateFiniteExact 64 F)
    (size : BitVec 64)
    (nLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (small : size.toNat ≤ 33806089496) (ticks : 4 * size.toNat ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_memeq) = (result,post) ∧
      state.clock ≤ post.clock + 4 * size.toNat ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut := by
  let entered := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state
  have initial : entered.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atN : entered.locals.lookup (ofString "n") = some (.val (.word size)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "n" from by decide] using nLocal
  obtain ⟨result,middle,run,cost,remaining,noTimeout,completed⟩ :=
    evaluate_memeq_alignment_choice_bounded_cap entered size 0 initial atN (by simp) small
      (by change 2 * size.toNat ≤ state.clock; omega)
  have sequence : ∃ result post, evaluateHOLFiniteState entered (.seq memeqAlignmentChoice memeqAfterAligned) = (result,post) ∧
      state.clock ≤ post.clock + 4 * size.toNat ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut := by
    rw [evaluateHOLFiniteState_seq_line780,run]
    cases result with
    | none =>
      obtain ⟨⟨index,localIndex,bounded⟩,localN⟩ := completed rfl
      obtain ⟨finalResult,post,tail,tailCost,tailRemaining,tailNoTimeout⟩ :=
        evaluate_memeq_byte_suffix_bounded_cap middle size index localIndex localN bounded small
          (by change state.clock ≤ middle.clock + 2 * size.toNat at cost; omega)
      exact ⟨finalResult,post,tail,(by change state.clock ≤ middle.clock + 2 * size.toNat at cost; omega),
        (by change middle.clock ≤ state.clock at remaining; omega),tailNoTimeout⟩
    | some result =>
      exact ⟨_,_,rfl,(by change state.clock ≤ middle.clock + 2 * size.toNat at cost; omega),remaining,noTimeout⟩
  obtain ⟨result,post,sequenceRun,total,remaining,noTimeout⟩ := sequence
  have full : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_memeq) =
      (result,{post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "i",state.locals.lookup (ofString "i"))}) := by
    rw [source_memeq_scoped_body,evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
    change evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state)
      (.seq (.ite memeqAlignmentCondition memeqAlignedBody .skip) memeqAfterAligned) = (result,post) at sequenceRun
    rw [sequenceRun]
  exact ⟨result,_,full,total,remaining,noTimeout⟩

#print axioms evaluate_memeq_alignment_choice_bounded_cap
#print axioms evaluate_memeq_body64_bounded_cap
end InitECandidate.Runtime
