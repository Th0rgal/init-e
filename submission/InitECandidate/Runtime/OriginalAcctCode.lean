import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_acctNew_lookup :
    originalRuntimeCode.lookup (ofString "acct_new") =
      some ([(ofString "nonce",.one),(ofString "balance",.comb [.one,.one,.one,.one]),(ofString "code_hash",.one)],sourceFunctionBody Guest.guestFn_acct_new,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "acct_new") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "acct_new") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "acct_new")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 364 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original364 :: declarations.drop 365 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 365)).reverse).all
          (fun entry => !((ofString "acct_new") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original364 :: declarations.drop 365) =
          (ofString "acct_new",[(ofString "nonce",ShapeHOL.one),(ofString "balance",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "code_hash",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_acct_new,ShapeHOL.one) ::
            functionsHOL (declarations.drop 365) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original364_eq]
        simp only [Guest.guestFn_acct_new,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "acct_new") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "acct_new") (functionsHOL (declarations.drop 365)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "acct_new") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

theorem originalRuntimeCode_acctEmpty_lookup :
    originalRuntimeCode.lookup (ofString "acct_empty") =
      some ([],sourceFunctionBody Guest.guestFn_acct_empty,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "acct_empty") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "acct_empty") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "acct_empty")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 365 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original365 :: declarations.drop 366 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 366)).reverse).all
          (fun entry => !((ofString "acct_empty") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original365 :: declarations.drop 366) =
          (ofString "acct_empty",[],sourceFunctionBody Guest.guestFn_acct_empty,ShapeHOL.one) ::
            functionsHOL (declarations.drop 366) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original365_eq]
        simp only [Guest.guestFn_acct_empty,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "acct_empty") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "acct_empty") (functionsHOL (declarations.drop 366)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "acct_empty") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

theorem originalRuntimeCode_preStateAccountW_lookup :
    originalRuntimeCode.lookup (ofString "get_pre_state_account") =
      some ([(ofString "addr",.one)],sourceFunctionBody Guest.guestFn_get_pre_state_account,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "get_pre_state_account") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "get_pre_state_account") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "get_pre_state_account")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 376 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original376 :: declarations.drop 377 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 377)).reverse).all
          (fun entry => !((ofString "get_pre_state_account") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original376 :: declarations.drop 377) =
          (ofString "get_pre_state_account",[(ofString "addr",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_get_pre_state_account,ShapeHOL.one) ::
            functionsHOL (declarations.drop 377) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original376_eq]
        simp only [Guest.guestFn_get_pre_state_account,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "get_pre_state_account") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "get_pre_state_account") (functionsHOL (declarations.drop 377)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "get_pre_state_account") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_acctNew_lookup
#print axioms originalRuntimeCode_acctEmpty_lookup
#print axioms originalRuntimeCode_preStateAccountW_lookup

end InitECandidate.Runtime
