import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_nodeNewHashed_lookup :
    originalRuntimeCode.lookup (ofString "node_new_hashed") =
      some ([(ofString "hash",.one)],sourceFunctionBody Guest.guestFn_node_new_hashed,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "node_new_hashed") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "node_new_hashed") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "node_new_hashed")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 258 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original258 :: declarations.drop 259 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 259)).reverse).all
          (fun entry => !((ofString "node_new_hashed") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original258 :: declarations.drop 259) =
          (ofString "node_new_hashed",[(ofString "hash",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_node_new_hashed,ShapeHOL.one) ::
            functionsHOL (declarations.drop 259) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original258_eq]
        simp only [Guest.guestFn_node_new_hashed,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "node_new_hashed") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "node_new_hashed") (functionsHOL (declarations.drop 259)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "node_new_hashed") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_nodeNewHashed_lookup

end InitECandidate.Runtime
