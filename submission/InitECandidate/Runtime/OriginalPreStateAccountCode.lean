import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_preStateAccount_lookup :
    originalRuntimeCode.lookup (ofString "get_pre_state_account_optional") =
      some ([(ofString "addr",.one)],sourceFunctionBody Guest.guestFn_get_pre_state_account_optional,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "get_pre_state_account_optional") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "get_pre_state_account_optional") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "get_pre_state_account_optional")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 375 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original375 :: declarations.drop 376 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 376)).reverse).all
          (fun entry => !((ofString "get_pre_state_account_optional") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original375 :: declarations.drop 376) =
          (ofString "get_pre_state_account_optional",[(ofString "addr",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_get_pre_state_account_optional,ShapeHOL.one) ::
            functionsHOL (declarations.drop 376) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original375_eq]
        simp only [Guest.guestFn_get_pre_state_account_optional,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "get_pre_state_account_optional") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "get_pre_state_account_optional") (functionsHOL (declarations.drop 376)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "get_pre_state_account_optional") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_preStateAccount_lookup

end InitECandidate.Runtime
