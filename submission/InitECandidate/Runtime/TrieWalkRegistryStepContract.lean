import InitECandidate.Runtime.TrieWalkRegistry
import InitECandidate.Runtime.TrieWalkStepContract
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A complete original traversal iteration retains all registry facts on
normal completion, selects a live/null node, and decreases its loop rank. -/
theorem evaluate_trieWalk_registry_step_contract {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (node nibs index length : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (bounded : index.toNat ≤ length.toNat)
    (small : length.toNat ≤ 64) (nodeNonzero : node ≠ 0) (member : node ∈ live)
    (registry : TrieWalkRegistry live extensions branches state)
    (nibbles : TrieNibbleRange state nibs length) (ticks : 257 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state trieWalkStep = (result,post) ∧
      state.clock ≤ post.clock + 257 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      result ≠ some .break ∧ result ≠ some .continue ∧
      (result = none → ∃ child next : BitVec 64,
        post.locals.lookup (ofString "node") = some (.val (.word child)) ∧
        post.locals.lookup (ofString "pos") = some (.val (.word next)) ∧
        post.locals.lookup (ofString "nibs") = some (.val (.word nibs)) ∧
        post.locals.lookup (ofString "nlen") = some (.val (.word length)) ∧
        next.toNat ≤ length.toNat ∧ (child = 0 ∨ child ∈ live) ∧
        post.code = originalRuntimeCode ∧ TrieWalkRegistry live extensions branches post ∧
        TrieNibbleRange post nibs length ∧ trieWalkLoopRank length post < trieWalkLoopRank length state) := by
  have bound := evaluate_trieWalk_step_bounded state node nibs index length nodeLocal nibsLocal posLocal nlenLocal code bounded small ticks
  have controls := evaluate_trieWalk_step_no_loop_control state
  cases run : evaluateHOLFiniteState state trieWalkStep with
  | mk result post =>
    rw [run] at bound controls
    dsimp only at bound controls
    refine ⟨result,post,rfl,bound.1,bound.2.1,bound.2.2,controls.1,controls.2,?_⟩
    intro normal
    subst result
    obtain ⟨child,next,atNode,atPos,atNibs,atLength,nextBound,memory,_,postCode⟩ :=
      evaluate_trieWalk_step_invariant state post node nibs index length nodeLocal nibsLocal posLocal nlenLocal code bounded (by omega) run
    obtain ⟨selected,selectedLocal,liveChild,decrease⟩ := evaluate_trieWalk_step_live_progress
      state post node nibs index length nodeLocal nibsLocal posLocal nlenLocal code bounded nodeNonzero
      (by omega) live extensions branches registry.order (registry.extensionKind node member)
      registry.extensionChildren registry.branchChildren (registry.branchKind node member) nibbles run
    have same : selected = child := by simpa using Option.some.inj (selectedLocal.symm.trans atNode)
    subst selected
    have metadata := evaluateHOLFiniteState_metadata state trieWalkStep
    rw [run] at metadata
    dsimp only at metadata
    exact ⟨child,next,atNode,atPos,atNibs,atLength,nextBound,liveChild,postCode.trans code,
      registry.after_memory memory,nibbles.after_frame memory metadata.2.1 metadata.2.2.1,decrease⟩

#print axioms evaluate_trieWalk_registry_step_contract
end InitECandidate.Runtime
