import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_lstUpsertIdx_lookup :
    originalRuntimeCode.lookup (ofString "lst_upsert_idx") =
      some ([(ofString "l",.one),(ofString "esz",.one),(ofString "idx",.one)],sourceFunctionBody Guest.guestFn_lst_upsert_idx,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "lst_upsert_idx") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "lst_upsert_idx") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "lst_upsert_idx")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 416 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original416 :: declarations.drop 417 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 417)).reverse).all
          (fun entry => !((ofString "lst_upsert_idx") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original416 :: declarations.drop 417) =
          (ofString "lst_upsert_idx",[(ofString "l",ShapeHOL.one),(ofString "esz",ShapeHOL.one),(ofString "idx",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_lst_upsert_idx,ShapeHOL.one) ::
            functionsHOL (declarations.drop 417) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original416_eq]
        simp only [Guest.guestFn_lst_upsert_idx,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "lst_upsert_idx") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "lst_upsert_idx") (functionsHOL (declarations.drop 417)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "lst_upsert_idx") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_lstUpsertIdx_lookup

theorem originalRuntimeCode_balListRemoveIdx_lookup :
    originalRuntimeCode.lookup (ofString "bal_list_remove_idx") =
      some ([(ofString "l",.one),(ofString "esz",.one),(ofString "idx",.one)],sourceFunctionBody Guest.guestFn_bal_list_remove_idx,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "bal_list_remove_idx") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "bal_list_remove_idx") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "bal_list_remove_idx")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 427 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original427 :: declarations.drop 428 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 428)).reverse).all
          (fun entry => !((ofString "bal_list_remove_idx") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original427 :: declarations.drop 428) =
          (ofString "bal_list_remove_idx",[(ofString "l",ShapeHOL.one),(ofString "esz",ShapeHOL.one),(ofString "idx",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_bal_list_remove_idx,ShapeHOL.one) ::
            functionsHOL (declarations.drop 428) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original427_eq]
        simp only [Guest.guestFn_bal_list_remove_idx,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "bal_list_remove_idx") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "bal_list_remove_idx") (functionsHOL (declarations.drop 428)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "bal_list_remove_idx") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_balListRemoveIdx_lookup

theorem originalRuntimeCode_balEnsureAccount_lookup :
    originalRuntimeCode.lookup (ofString "bal_ensure_account") =
      some ([(ofString "addr",.one)],sourceFunctionBody Guest.guestFn_bal_ensure_account,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "bal_ensure_account") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "bal_ensure_account") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "bal_ensure_account")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 415 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original415 :: declarations.drop 416 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 416)).reverse).all
          (fun entry => !((ofString "bal_ensure_account") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original415 :: declarations.drop 416) =
          (ofString "bal_ensure_account",[(ofString "addr",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_bal_ensure_account,ShapeHOL.one) ::
            functionsHOL (declarations.drop 416) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original415_eq]
        simp only [Guest.guestFn_bal_ensure_account,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "bal_ensure_account") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "bal_ensure_account") (functionsHOL (declarations.drop 416)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "bal_ensure_account") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_balEnsureAccount_lookup

theorem originalRuntimeCode_balRemoveChange_lookup :
    originalRuntimeCode.lookup (ofString "bal_remove_change") =
      some ([(ofString "addr",.one),(ofString "which",.one),(ofString "esz",.one),(ofString "idx",.one)],sourceFunctionBody Guest.guestFn_bal_remove_change,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "bal_remove_change") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "bal_remove_change") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "bal_remove_change")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 428 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original428 :: declarations.drop 429 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 429)).reverse).all
          (fun entry => !((ofString "bal_remove_change") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original428 :: declarations.drop 429) =
          (ofString "bal_remove_change",[(ofString "addr",ShapeHOL.one),(ofString "which",ShapeHOL.one),(ofString "esz",ShapeHOL.one),(ofString "idx",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_bal_remove_change,ShapeHOL.one) ::
            functionsHOL (declarations.drop 429) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original428_eq]
        simp only [Guest.guestFn_bal_remove_change,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "bal_remove_change") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "bal_remove_change") (functionsHOL (declarations.drop 429)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "bal_remove_change") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_balRemoveChange_lookup

theorem originalRuntimeCode_addBalanceChange_lookup :
    originalRuntimeCode.lookup (ofString "add_balance_change") =
      some ([(ofString "addr",.one),(ofString "idx",.one),(ofString "post_balance",(.comb [.one,.one,.one,.one]))],sourceFunctionBody Guest.guestFn_add_balance_change,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "add_balance_change") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "add_balance_change") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "add_balance_change")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 419 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original419 :: declarations.drop 420 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 420)).reverse).all
          (fun entry => !((ofString "add_balance_change") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original419 :: declarations.drop 420) =
          (ofString "add_balance_change",[(ofString "addr",ShapeHOL.one),(ofString "idx",ShapeHOL.one),(ofString "post_balance",(ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]))],sourceFunctionBody Guest.guestFn_add_balance_change,ShapeHOL.one) ::
            functionsHOL (declarations.drop 420) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original419_eq]
        simp only [Guest.guestFn_add_balance_change,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "add_balance_change") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "add_balance_change") (functionsHOL (declarations.drop 420)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "add_balance_change") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_addBalanceChange_lookup

theorem originalRuntimeCode_addNonceChange_lookup :
    originalRuntimeCode.lookup (ofString "add_nonce_change") =
      some ([(ofString "addr",.one),(ofString "idx",.one),(ofString "new_nonce",.one)],sourceFunctionBody Guest.guestFn_add_nonce_change,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "add_nonce_change") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "add_nonce_change") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "add_nonce_change")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 420 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original420 :: declarations.drop 421 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 421)).reverse).all
          (fun entry => !((ofString "add_nonce_change") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original420 :: declarations.drop 421) =
          (ofString "add_nonce_change",[(ofString "addr",ShapeHOL.one),(ofString "idx",ShapeHOL.one),(ofString "new_nonce",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_add_nonce_change,ShapeHOL.one) ::
            functionsHOL (declarations.drop 421) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original420_eq]
        simp only [Guest.guestFn_add_nonce_change,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "add_nonce_change") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "add_nonce_change") (functionsHOL (declarations.drop 421)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "add_nonce_change") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_addNonceChange_lookup

theorem originalRuntimeCode_addCodeChange_lookup :
    originalRuntimeCode.lookup (ofString "add_code_change") =
      some ([(ofString "addr",.one),(ofString "idx",.one),(ofString "code",.one),(ofString "code_len",.one)],sourceFunctionBody Guest.guestFn_add_code_change,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "add_code_change") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "add_code_change") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "add_code_change")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 421 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original421 :: declarations.drop 422 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 422)).reverse).all
          (fun entry => !((ofString "add_code_change") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original421 :: declarations.drop 422) =
          (ofString "add_code_change",[(ofString "addr",ShapeHOL.one),(ofString "idx",ShapeHOL.one),(ofString "code",ShapeHOL.one),(ofString "code_len",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_add_code_change,ShapeHOL.one) ::
            functionsHOL (declarations.drop 422) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original421_eq]
        simp only [Guest.guestFn_add_code_change,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "add_code_change") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "add_code_change") (functionsHOL (declarations.drop 422)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "add_code_change") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_addCodeChange_lookup

theorem originalRuntimeCode_addStorageWrite_lookup :
    originalRuntimeCode.lookup (ofString "add_storage_write") =
      some ([(ofString "addr",.one),(ofString "slot",.one),(ofString "idx",.one),(ofString "new_value",(.comb [.one,.one,.one,.one]))],sourceFunctionBody Guest.guestFn_add_storage_write,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "add_storage_write") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "add_storage_write") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "add_storage_write")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 417 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original417 :: declarations.drop 418 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 418)).reverse).all
          (fun entry => !((ofString "add_storage_write") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original417 :: declarations.drop 418) =
          (ofString "add_storage_write",[(ofString "addr",ShapeHOL.one),(ofString "slot",ShapeHOL.one),(ofString "idx",ShapeHOL.one),(ofString "new_value",(ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]))],sourceFunctionBody Guest.guestFn_add_storage_write,ShapeHOL.one) ::
            functionsHOL (declarations.drop 418) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original417_eq]
        simp only [Guest.guestFn_add_storage_write,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "add_storage_write") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "add_storage_write") (functionsHOL (declarations.drop 418)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "add_storage_write") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_addStorageWrite_lookup

theorem originalRuntimeCode_removeStorageWrite_lookup :
    originalRuntimeCode.lookup (ofString "remove_storage_write") =
      some ([(ofString "addr",.one),(ofString "slot",.one),(ofString "idx",.one)],sourceFunctionBody Guest.guestFn_remove_storage_write,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "remove_storage_write") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "remove_storage_write") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "remove_storage_write")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 429 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original429 :: declarations.drop 430 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 430)).reverse).all
          (fun entry => !((ofString "remove_storage_write") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original429 :: declarations.drop 430) =
          (ofString "remove_storage_write",[(ofString "addr",ShapeHOL.one),(ofString "slot",ShapeHOL.one),(ofString "idx",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_remove_storage_write,ShapeHOL.one) ::
            functionsHOL (declarations.drop 430) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original429_eq]
        simp only [Guest.guestFn_remove_storage_write,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "remove_storage_write") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "remove_storage_write") (functionsHOL (declarations.drop 430)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "remove_storage_write") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_removeStorageWrite_lookup

theorem originalRuntimeCode_idxStartAccount_lookup :
    originalRuntimeCode.lookup (ofString "idx_start_account") =
      some ([(ofString "addr",.one)],sourceFunctionBody Guest.guestFn_idx_start_account,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "idx_start_account") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "idx_start_account") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "idx_start_account")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 425 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original425 :: declarations.drop 426 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 426)).reverse).all
          (fun entry => !((ofString "idx_start_account") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original425 :: declarations.drop 426) =
          (ofString "idx_start_account",[(ofString "addr",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_idx_start_account,ShapeHOL.one) ::
            functionsHOL (declarations.drop 426) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original425_eq]
        simp only [Guest.guestFn_idx_start_account,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "idx_start_account") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "idx_start_account") (functionsHOL (declarations.drop 426)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "idx_start_account") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_idxStartAccount_lookup

theorem originalRuntimeCode_idxStartStorage_lookup :
    originalRuntimeCode.lookup (ofString "idx_start_storage") =
      some ([(ofString "addr",.one),(ofString "key",.one)],sourceFunctionBody Guest.guestFn_idx_start_storage,(.comb [.one,.one,.one,.one])) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "idx_start_storage") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "idx_start_storage") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "idx_start_storage")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 426 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original426 :: declarations.drop 427 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 427)).reverse).all
          (fun entry => !((ofString "idx_start_storage") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original426 :: declarations.drop 427) =
          (ofString "idx_start_storage",[(ofString "addr",ShapeHOL.one),(ofString "key",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_idx_start_storage,(ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one])) ::
            functionsHOL (declarations.drop 427) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original426_eq]
        simp only [Guest.guestFn_idx_start_storage,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "idx_start_storage") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "idx_start_storage") (functionsHOL (declarations.drop 427)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "idx_start_storage") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_idxStartStorage_lookup

theorem originalRuntimeCode_updateBuilderFromTx_lookup :
    originalRuntimeCode.lookup (ofString "update_builder_from_tx") =
      some ([],sourceFunctionBody Guest.guestFn_update_builder_from_tx,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "update_builder_from_tx") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "update_builder_from_tx") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "update_builder_from_tx")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 430 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original430 :: declarations.drop 431 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 431)).reverse).all
          (fun entry => !((ofString "update_builder_from_tx") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original430 :: declarations.drop 431) =
          (ofString "update_builder_from_tx",[],sourceFunctionBody Guest.guestFn_update_builder_from_tx,ShapeHOL.one) ::
            functionsHOL (declarations.drop 431) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original430_eq]
        simp only [Guest.guestFn_update_builder_from_tx,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "update_builder_from_tx") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "update_builder_from_tx") (functionsHOL (declarations.drop 431)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "update_builder_from_tx") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_updateBuilderFromTx_lookup

theorem originalRuntimeCode_mergeTxIntoBlock_lookup :
    originalRuntimeCode.lookup (ofString "merge_tx_into_block") =
      some ([],sourceFunctionBody Guest.guestFn_merge_tx_into_block,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "merge_tx_into_block") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "merge_tx_into_block") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "merge_tx_into_block")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 404 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original404 :: declarations.drop 405 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 405)).reverse).all
          (fun entry => !((ofString "merge_tx_into_block") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original404 :: declarations.drop 405) =
          (ofString "merge_tx_into_block",[],sourceFunctionBody Guest.guestFn_merge_tx_into_block,ShapeHOL.one) ::
            functionsHOL (declarations.drop 405) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original404_eq]
        simp only [Guest.guestFn_merge_tx_into_block,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "merge_tx_into_block") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "merge_tx_into_block") (functionsHOL (declarations.drop 405)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "merge_tx_into_block") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_mergeTxIntoBlock_lookup

end InitECandidate.Runtime
