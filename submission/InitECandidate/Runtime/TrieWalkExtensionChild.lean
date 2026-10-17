import InitECandidate.Runtime.TrieWalkExtensionAdvance
import InitECandidate.Runtime.LocalAssignNormalValue
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_trieWalk_extension_node_expression : trieWalkExtensionNodeExpression =
    .load .one (.op .add [.var .local (ofString "node"),.const 48]) := by
  simp only [trieWalkExtensionNodeExpression,trieWalkExtensionAdvance,trieWalkExtensionContinuation,
    trieWalkExtensionComparison,trieWalkExtensionBranch,trieWalkStep,trieWalkLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Successful original extension updates select exactly the child pointer
at node+48 in the update's entry memory. Invalid loads cannot complete normally. -/
theorem evaluate_trieWalk_extension_advance_child {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (node index size : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "sl") = some (.val (.word size)))
    (run : evaluateHOLFiniteState state trieWalkExtensionAdvance = (none,post)) :
    ∃ child : BitVec 64, state.memaddrs (node + BitVec.ofNat 64 48) ∧
      state.memory (node + BitVec.ofNat 64 48) = .word child ∧
      post.locals.lookup (ofString "node") = some (.val (.word child)) := by
  classical
  let advanced := setVarHOLFinite (ofString "pos") (.val (.word (index + size))) state
  have update : evaluateHOLFiniteState state
      (.assign .local (ofString "pos") (.op .add [.var .local (ofString "pos"),.var .local (ofString "sl")])) = (none,advanced) := by
    simp [advanced,evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,posLocal,sizeLocal,
      wordOpHOL,wordOp,valueIsWord,valueWord,lookupKvarHOLExact,isValidValueHOLExact,setKvarHOLFinite,shapeOfHOLExact,shapeEqHOL]
  rw [source_trieWalk_extension_advance,evaluateHOLFiniteState_seq_line780,update] at run
  change evaluateHOLFiniteState advanced (.assign .local (ofString "node") trieWalkExtensionNodeExpression) = (none,post) at run
  obtain ⟨value,evaluated,assigned⟩ := evaluate_local_assign_normal_value advanced post (ofString "node") trieWalkExtensionNodeExpression run
  by_cases accessible : state.memaddrs (node + BitVec.ofNat 64 48)
  · cases memory : state.memory (node + BitVec.ofNat 64 48) with
    | word child =>
      have actual : @evalHOLExact 64 F _ advanced.toExact
          (fun address => Classical.propDecidable (advanced.memaddrs address)) trieWalkExtensionNodeExpression = some (.val (.word child)) := by
        rw [source_trieWalk_extension_node_expression]
        simp [evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,advanced,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nodeLocal,show ofString "pos" ≠ ofString "node" from by decide,accessible,memory]
      have valueEq := Option.some.inj (evaluated.symm.trans actual)
      subst value
      refine ⟨child,accessible,rfl,?_⟩
      rw [assigned]
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · have failed : @evalHOLExact 64 F _ advanced.toExact
        (fun address => Classical.propDecidable (advanced.memaddrs address)) trieWalkExtensionNodeExpression = none := by
      rw [source_trieWalk_extension_node_expression]
      simp [evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,advanced,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nodeLocal,show ofString "pos" ≠ ofString "node" from by decide,accessible]
    rw [failed] at evaluated
    cases evaluated

/-- The same child identity holds through the original mismatch guard. -/
theorem evaluate_trieWalk_extension_continuation_child {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (node index size : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (posLocal : state.locals.lookup (ofString "pos") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "sl") = some (.val (.word size)))
    (run : evaluateHOLFiniteState state trieWalkExtensionContinuation = (none,post)) :
    ∃ child : BitVec 64, state.memaddrs (node + BitVec.ofNat 64 48) ∧
      state.memory (node + BitVec.ofNat 64 48) = .word child ∧
      post.locals.lookup (ofString "node") = some (.val (.word child)) :=
  evaluate_trieWalk_extension_advance_child state post node index size nodeLocal posLocal sizeLocal
    (evaluate_trieWalk_extension_normal_advance state post run)

#print axioms source_trieWalk_extension_node_expression
#print axioms evaluate_trieWalk_extension_advance_child
#print axioms evaluate_trieWalk_extension_continuation_child
end InitECandidate.Runtime
