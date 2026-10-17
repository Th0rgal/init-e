import InitECandidate.Runtime.TrieWalkKindDispatchBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_trieWalk_step_body : trieWalkStep =
    .dec (ofString "k") .one (.load .one (.op .add [.var .local (ofString "node"),.const 0])) trieWalkAfterKind := by
  simp only [trieWalkStep,trieWalkAfterKind,trieWalkLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The complete original trie traversal iteration has nested source-clock
cost at most257 ticks. The enclosing while-loop entry tick is separate.
All node kinds and invalid reads are included under the key-position invariant. -/
theorem evaluate_trieWalk_step_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (node nibs index length : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (bounded : index.toNat ≤ length.toNat)
    (small : length.toNat ≤ 64) (ticks : 257 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state trieWalkStep;
    state.clock ≤ evaluated.2.clock + 257 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  classical
  by_cases accessible : state.memaddrs node
  · cases memory : state.memory node with
    | word kind =>
      have initialized : @evalHOLExact 64 F _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address))
          (.load .one (.op .add [.var .local (ofString "node"),.const 0])) = some (.val (.word kind)) := by
        simp [evalHOLExact,evalListHOLExact,nodeLocal,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,accessible,memory]
      let entered := setVarHOLFinite (ofString "k") (.val (.word kind)) state
      have kept : ∀ name, name ≠ ofString "k" → entered.locals.lookup name = state.locals.lookup name := by
        intro name different
        simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
      have kindLocal : entered.locals.lookup (ofString "k") = some (.val (.word kind)) := by
        simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      have bound := evaluate_trieWalk_after_kind_bounded entered node nibs index length kind
        ((kept _ (by decide)).trans nodeLocal) ((kept _ (by decide)).trans nibsLocal)
        ((kept _ (by decide)).trans posLocal) ((kept _ (by decide)).trans nlenLocal)
        kindLocal code bounded small ticks
      rw [source_trieWalk_step_body,evaluateHOLFiniteState_dec_total]
      simp only [initialized,shapeOfHOLExact,shapeEqHOL,if_true]
      change state.clock ≤ (evaluateHOLFiniteState entered trieWalkAfterKind).2.clock + 257 ∧
        (evaluateHOLFiniteState entered trieWalkAfterKind).2.clock ≤ state.clock ∧
        (evaluateHOLFiniteState entered trieWalkAfterKind).1 ≠ some .timeOut
      exact bound
  · have initialized : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.load .one (.op .add [.var .local (ofString "node"),.const 0])) = none := by
      simp [evalHOLExact,evalListHOLExact,nodeLocal,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,accessible]
    rw [source_trieWalk_step_body,evaluateHOLFiniteState_dec_total]
    simp only [initialized]
    exact ⟨by omega,by omega,by simp⟩

#print axioms source_trieWalk_step_body
#print axioms evaluate_trieWalk_step_bounded
end InitECandidate.Runtime
