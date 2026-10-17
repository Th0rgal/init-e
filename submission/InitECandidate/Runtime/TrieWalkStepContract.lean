import InitECandidate.Runtime.TrieWalkStepControl
import InitECandidate.Runtime.TrieWalkStepInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete original iteration contract: bounded nested clock cost,
terminal exits without loop control, and actual invariant/rank progress on
normal completion. Zero-length child ordering remains explicit. -/
theorem evaluate_trieWalk_step_contract {F : Type} (state : PanSemStateFiniteExact 64 F)
    (node nibs index length : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (bounded : index.toNat ≤ length.toNat)
    (small : length.toNat ≤ 64) (nodeNonzero : node ≠ 0) (ticks : 257 ≤ state.clock)
    (emptyChildOrder : ∀ child : BitVec 64,
      state.memory (node + BitVec.ofNat 64 40) = .word 0 →
      state.memory (node + BitVec.ofNat 64 48) = .word child → child.toNat < node.toNat) :
    ∃ result post, evaluateHOLFiniteState state trieWalkStep = (result,post) ∧
      state.clock ≤ post.clock + 257 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      result ≠ some .break ∧ result ≠ some .continue ∧
      (result = none → ∃ child next : BitVec 64,
        post.locals.lookup (ofString "node") = some (.val (.word child)) ∧
        post.locals.lookup (ofString "pos") = some (.val (.word next)) ∧
        post.locals.lookup (ofString "nibs") = some (.val (.word nibs)) ∧
        post.locals.lookup (ofString "nlen") = some (.val (.word length)) ∧
        next.toNat ≤ length.toNat ∧ post.memory = state.memory ∧ post.globals = state.globals ∧
        post.code = state.code ∧ trieWalkLoopRank length post < trieWalkLoopRank length state) := by
  have bound := evaluate_trieWalk_step_bounded state node nibs index length nodeLocal nibsLocal posLocal nlenLocal code bounded small ticks
  have controls := evaluate_trieWalk_step_no_loop_control state
  cases run : evaluateHOLFiniteState state trieWalkStep with
  | mk result post =>
    rw [run] at bound controls
    dsimp only at bound controls
    refine ⟨result,post,rfl,bound.1,bound.2.1,bound.2.2,controls.1,controls.2,?_⟩
    intro normal
    subst result
    obtain ⟨child,next,atNode,atPos,atNibs,atLength,nextBound,memory,globals,postCode⟩ :=
      evaluate_trieWalk_step_invariant state post node nibs index length nodeLocal nibsLocal posLocal nlenLocal code bounded (by omega) run
    have decrease := evaluate_trieWalk_step_rank state post node nibs index length nodeLocal nibsLocal posLocal nlenLocal
      code bounded nodeNonzero (by omega) emptyChildOrder run
    exact ⟨child,next,atNode,atPos,atNibs,atLength,nextBound,memory,globals,postCode,decrease⟩

#print axioms evaluate_trieWalk_step_contract
end InitECandidate.Runtime
