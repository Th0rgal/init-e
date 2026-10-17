import InitECandidate.Runtime.TrieWalkExtensionGuardBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_trieWalk_extension_branch : trieWalkExtensionBranch =
    .dec (ofString "sl") .one (.load .one (.op .add [.var .local (ofString "node"),.const 40])) trieWalkExtensionAfterLength := by
  simp only [trieWalkExtensionBranch,trieWalkExtensionAfterLength,trieWalkStep,trieWalkLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The complete original extension branch, from loading its segment length
through the position/node updates, uses at most257 source ticks. -/
theorem evaluate_trieWalk_extension_branch_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (node nibs pos nlen : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word pos)))
    (nlenLocal : state.locals.lookup (ofString "nlen") = some (.val (.word nlen)))
    (code : state.code = originalRuntimeCode) (position : pos.toNat ≤ nlen.toNat)
    (keySize : nlen.toNat ≤ 64) (ticks : 257 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state trieWalkExtensionBranch;
    state.clock ≤ evaluated.2.clock + 257 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  classical
  by_cases accessible : state.memaddrs (node + BitVec.ofNat 64 40)
  · cases memory : state.memory (node + BitVec.ofNat 64 40) with
    | word size =>
      have initialized : @evalHOLExact 64 F _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address))
          (.load .one (.op .add [.var .local (ofString "node"),.const 40])) = some (.val (.word size)) := by
        simp [evalHOLExact,evalListHOLExact,nodeLocal,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,accessible,memory]
      let entered := setVarHOLFinite (ofString "sl") (.val (.word size)) state
      have kept : ∀ name, name ≠ ofString "sl" → entered.locals.lookup name = state.locals.lookup name := by
        intro name different
        simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
      have lengthLocal : entered.locals.lookup (ofString "sl") = some (.val (.word size)) := by
        simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      have bound := evaluate_trieWalk_extension_after_length_bounded entered node nibs pos size nlen
        (by rw [kept _ (by decide)]; exact nodeLocal) (by rw [kept _ (by decide)]; exact nibsLocal)
        (by rw [kept _ (by decide)]; exact posLocal) lengthLocal
        (by rw [kept _ (by decide)]; exact nlenLocal) code position keySize ticks
      rw [source_trieWalk_extension_branch,evaluateHOLFiniteState_dec_total]
      simp only [initialized,shapeOfHOLExact,shapeEqHOL,if_true]
      change state.clock ≤ (evaluateHOLFiniteState entered trieWalkExtensionAfterLength).2.clock + 257 ∧
        (evaluateHOLFiniteState entered trieWalkExtensionAfterLength).2.clock ≤ state.clock ∧
        (evaluateHOLFiniteState entered trieWalkExtensionAfterLength).1 ≠ some .timeOut
      exact bound
  · have initialized : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.load .one (.op .add [.var .local (ofString "node"),.const 40])) = none := by
      simp [evalHOLExact,evalListHOLExact,nodeLocal,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,accessible]
    rw [source_trieWalk_extension_branch,evaluateHOLFiniteState_dec_total]
    simp only [initialized]
    exact ⟨by omega,by omega,by simp⟩

#print axioms source_trieWalk_extension_branch
#print axioms evaluate_trieWalk_extension_branch_bounded
end InitECandidate.Runtime
