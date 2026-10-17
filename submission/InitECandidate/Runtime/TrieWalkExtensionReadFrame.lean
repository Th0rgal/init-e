import InitECandidate.Runtime.TrieWalkComparisonReadFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete original extension branch preserves memory and globals,
including invalid loads, shape failures, early returns and timeouts. -/
theorem evaluate_trieWalk_extension_branch_read_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (node nibs pos : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsLocal : state.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word pos)))
    (code : state.code = originalRuntimeCode) :
    let evaluated := evaluateHOLFiniteState state trieWalkExtensionBranch;
    evaluated.2.memory = state.memory ∧ evaluated.2.globals = state.globals := by
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
      have bound := evaluate_trieWalk_extension_guard_read_frame entered node nibs pos size
        (by rw [kept _ (by decide)]; exact nodeLocal) (by rw [kept _ (by decide)]; exact nibsLocal)
        (by rw [kept _ (by decide)]; exact posLocal) lengthLocal code
      rw [source_trieWalk_extension_branch,evaluateHOLFiniteState_dec_total]
      simp only [initialized,shapeOfHOLExact,shapeEqHOL,if_true]
      change (evaluateHOLFiniteState entered trieWalkExtensionAfterLength).2.memory = state.memory ∧
        (evaluateHOLFiniteState entered trieWalkExtensionAfterLength).2.globals = state.globals
      exact bound
  · have initialized : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.load .one (.op .add [.var .local (ofString "node"),.const 40])) = none := by
      simp [evalHOLExact,evalListHOLExact,nodeLocal,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,accessible]
    rw [source_trieWalk_extension_branch,evaluateHOLFiniteState_dec_total]
    simp only [initialized]
    simp

#print axioms evaluate_trieWalk_extension_branch_read_frame
end InitECandidate.Runtime
