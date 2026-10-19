import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_acctCopy_lookup :
    originalRuntimeCode.lookup (ofString "acct_copy") =
      some ([(ofString "a",.one)],sourceFunctionBody Guest.guestFn_acct_copy,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "acct_copy") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "acct_copy") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "acct_copy")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 366 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original366 :: declarations.drop 367 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 367)).reverse).all
          (fun entry => !((ofString "acct_copy") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original366 :: declarations.drop 367) =
          (ofString "acct_copy",[(ofString "a",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_acct_copy,ShapeHOL.one) ::
            functionsHOL (declarations.drop 367) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original366_eq]
        simp only [Guest.guestFn_acct_copy,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "acct_copy") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "acct_copy") (functionsHOL (declarations.drop 367)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "acct_copy") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

theorem originalRuntimeCode_setAccount_lookup :
    originalRuntimeCode.lookup (ofString "set_account") =
      some ([(ofString "addr",.one),(ofString "a",.one)],sourceFunctionBody Guest.guestFn_set_account,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "set_account") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "set_account") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "set_account")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 390 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original390 :: declarations.drop 391 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 391)).reverse).all
          (fun entry => !((ofString "set_account") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original390 :: declarations.drop 391) =
          (ofString "set_account",[(ofString "addr",ShapeHOL.one),(ofString "a",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_set_account,ShapeHOL.one) ::
            functionsHOL (declarations.drop 391) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original390_eq]
        simp only [Guest.guestFn_set_account,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "set_account") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "set_account") (functionsHOL (declarations.drop 391)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "set_account") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

theorem originalRuntimeCode_destroyAccount_lookup :
    originalRuntimeCode.lookup (ofString "destroy_account") =
      some ([(ofString "addr",.one)],sourceFunctionBody Guest.guestFn_destroy_account,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "destroy_account") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "destroy_account") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "destroy_account")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 393 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original393 :: declarations.drop 394 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 394)).reverse).all
          (fun entry => !((ofString "destroy_account") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original393 :: declarations.drop 394) =
          (ofString "destroy_account",[(ofString "addr",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_destroy_account,ShapeHOL.one) ::
            functionsHOL (declarations.drop 394) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original393_eq]
        simp only [Guest.guestFn_destroy_account,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "destroy_account") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "destroy_account") (functionsHOL (declarations.drop 394)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "destroy_account") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

theorem originalRuntimeCode_modifyStateCommit_lookup :
    originalRuntimeCode.lookup (ofString "modify_state_commit") =
      some ([(ofString "addr",.one),(ofString "a",.one)],sourceFunctionBody Guest.guestFn_modify_state_commit,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "modify_state_commit") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "modify_state_commit") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "modify_state_commit")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 394 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original394 :: declarations.drop 395 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 395)).reverse).all
          (fun entry => !((ofString "modify_state_commit") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original394 :: declarations.drop 395) =
          (ofString "modify_state_commit",[(ofString "addr",ShapeHOL.one),(ofString "a",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_modify_state_commit,ShapeHOL.one) ::
            functionsHOL (declarations.drop 395) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original394_eq]
        simp only [Guest.guestFn_modify_state_commit,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "modify_state_commit") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "modify_state_commit") (functionsHOL (declarations.drop 395)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "modify_state_commit") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

theorem originalRuntimeCode_setAccountBalance_lookup :
    originalRuntimeCode.lookup (ofString "set_account_balance") =
      some ([(ofString "addr",.one),(ofString "amount",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_set_account_balance,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "set_account_balance") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "set_account_balance") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "set_account_balance")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 400 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original400 :: declarations.drop 401 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 401)).reverse).all
          (fun entry => !((ofString "set_account_balance") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original400 :: declarations.drop 401) =
          (ofString "set_account_balance",[(ofString "addr",ShapeHOL.one),(ofString "amount",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_set_account_balance,ShapeHOL.one) ::
            functionsHOL (declarations.drop 401) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original400_eq]
        simp only [Guest.guestFn_set_account_balance,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "set_account_balance") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "set_account_balance") (functionsHOL (declarations.drop 401)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "set_account_balance") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

theorem originalRuntimeCode_incrementNonce_lookup :
    originalRuntimeCode.lookup (ofString "increment_nonce") =
      some ([(ofString "addr",.one)],sourceFunctionBody Guest.guestFn_increment_nonce,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "increment_nonce") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "increment_nonce") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "increment_nonce")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 401 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original401 :: declarations.drop 402 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 402)).reverse).all
          (fun entry => !((ofString "increment_nonce") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original401 :: declarations.drop 402) =
          (ofString "increment_nonce",[(ofString "addr",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_increment_nonce,ShapeHOL.one) ::
            functionsHOL (declarations.drop 402) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original401_eq]
        simp only [Guest.guestFn_increment_nonce,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "increment_nonce") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "increment_nonce") (functionsHOL (declarations.drop 402)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "increment_nonce") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_acctCopy_lookup
#print axioms originalRuntimeCode_setAccount_lookup
#print axioms originalRuntimeCode_destroyAccount_lookup
#print axioms originalRuntimeCode_modifyStateCommit_lookup
#print axioms originalRuntimeCode_setAccountBalance_lookup
#print axioms originalRuntimeCode_incrementNonce_lookup

end InitECandidate.Runtime
