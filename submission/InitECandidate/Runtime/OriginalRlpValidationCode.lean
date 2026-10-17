import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_rlpValidationBody_lookup :
    originalRuntimeCode.lookup (ofString "_rlp_validate_items_body") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn__rlp_validate_items_body,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "_rlp_validate_items_body") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "_rlp_validate_items_body") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "_rlp_validate_items_body")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 111 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original111 :: declarations.drop 112 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 112)).reverse).all
          (fun entry => !((ofString "_rlp_validate_items_body") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original111 :: declarations.drop 112) =
          (ofString "_rlp_validate_items_body",[(ofString "p",ShapeHOL.one),(ofString "len",ShapeHOL.one)],sourceFunctionBody Guest.guestFn__rlp_validate_items_body,ShapeHOL.one) ::
            functionsHOL (declarations.drop 112) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original111_eq]
        simp only [Guest.guestFn__rlp_validate_items_body,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "_rlp_validate_items_body") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "_rlp_validate_items_body") (functionsHOL (declarations.drop 112)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "_rlp_validate_items_body") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_rlpValidationBody_lookup

end InitECandidate.Runtime
