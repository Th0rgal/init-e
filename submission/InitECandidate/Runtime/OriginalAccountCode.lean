import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_accountOptional_lookup :
    originalRuntimeCode.lookup (ofString "get_account_optional") =
      some ([(ofString "addr",.one)],sourceFunctionBody Guest.guestFn_get_account_optional,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "get_account_optional") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "get_account_optional") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "get_account_optional")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 377 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original377 :: declarations.drop 378 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 378)).reverse).all
          (fun entry => !((ofString "get_account_optional") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original377 :: declarations.drop 378) =
          (ofString "get_account_optional",[(ofString "addr",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_get_account_optional,ShapeHOL.one) ::
            functionsHOL (declarations.drop 378) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original377_eq]
        simp only [Guest.guestFn_get_account_optional,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "get_account_optional") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "get_account_optional") (functionsHOL (declarations.drop 378)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "get_account_optional") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

theorem originalRuntimeCode_account_lookup :
    originalRuntimeCode.lookup (ofString "get_account") =
      some ([(ofString "addr",.one)],sourceFunctionBody Guest.guestFn_get_account,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "get_account") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "get_account") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "get_account")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 378 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original378 :: declarations.drop 379 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 379)).reverse).all
          (fun entry => !((ofString "get_account") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original378 :: declarations.drop 379) =
          (ofString "get_account",[(ofString "addr",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_get_account,ShapeHOL.one) ::
            functionsHOL (declarations.drop 379) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original378_eq]
        simp only [Guest.guestFn_get_account,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "get_account") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "get_account") (functionsHOL (declarations.drop 379)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "get_account") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_accountOptional_lookup
#print axioms originalRuntimeCode_account_lookup

end InitECandidate.Runtime
