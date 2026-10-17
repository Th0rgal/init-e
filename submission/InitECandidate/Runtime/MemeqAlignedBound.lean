import InitECandidate.Runtime.MemeqWordLoopsBound
import InitECandidate.Runtime.MemeqFastPrefixFrame
import InitECandidate.Runtime.PanSeqAssoc
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_memeq_aligned_group {F : Type} (state : PanSemStateFiniteExact 64 F) :
    evaluateHOLFiniteState state memeqAlignedBody =
      evaluateHOLFiniteState state (.seq memeqFastPrefix memeqWordLoops) := by
  let first : ProgHOL 64 := .ite (.cmp .equal (.var .local (ofString "n")) (.const 20)) memeqFast20 .skip
  let second : ProgHOL 64 := .ite (.cmp .equal (.var .local (ofString "n")) (.const 32)) memeqFast32 .skip
  let third : ProgHOL 64 := .ite (.cmp .equal (.var .local (ofString "n")) (.const 52)) memeqFast52 .skip
  change evaluateHOLFiniteState state (.seq first (.seq second (.seq third memeqWordLoops))) =
    evaluateHOLFiniteState state (.seq (.seq first (.seq second third)) memeqWordLoops)
  rw [evaluate_seq_assoc]
  simp only [evaluateHOLFiniteState_seq_line780]
  cases firstRun : evaluateHOLFiniteState state first with
  | mk result middle =>
    cases result with
    | some result => rfl
    | none =>
      cases secondRun : evaluateHOLFiniteState middle second with
      | mk result post => cases result <;> rfl

/-- All aligned comparison branches, including the fixed20/32/52-byte fast
paths, cost at most2n source ticks for n≤64. -/
theorem evaluate_memeq_aligned_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (size index : BitVec 64)
    (initial : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (nLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (bounded : index.toNat ≤ size.toNat) (small : size.toNat ≤ 64) (ticks : 2 * size.toNat ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state memeqAlignedBody = (result,post) ∧
      state.clock ≤ post.clock + 2 * size.toNat ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → MemeqByteInvariant size post) := by
  have facts := memeq_fast_prefix_frame (F := F) state
  cases prefixRun : evaluateHOLFiniteState state memeqFastPrefix with
  | mk result middle =>
    rw [prefixRun] at facts
    dsimp only at facts
    rw [evaluate_memeq_aligned_group,evaluateHOLFiniteState_seq_line780,prefixRun]
    cases result with
    | none =>
      have equal := facts.2.2 rfl
      subst middle
      exact evaluate_memeq_word_loops_bounded state size index initial nLocal bounded small ticks
    | some result =>
      exact ⟨_,_,rfl,by omega,by omega,facts.2.1,(by intro impossible; cases impossible)⟩

#print axioms evaluate_memeq_aligned_group
#print axioms evaluate_memeq_aligned_bounded
end InitECandidate.Runtime
