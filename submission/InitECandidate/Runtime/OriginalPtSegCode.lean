import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_teNew_lookup :
    originalRuntimeCode.lookup (ofString "te_new") =
      some ([],sourceFunctionBody Guest.guestFn_te_new,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "te_new") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "te_new") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "te_new")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 908 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original908 :: declarations.drop 909 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 909)).reverse).all
          (fun entry => !((ofString "te_new") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original908 :: declarations.drop 909) =
          (ofString "te_new",[],sourceFunctionBody Guest.guestFn_te_new,ShapeHOL.one) ::
            functionsHOL (declarations.drop 909) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original908_eq]
        simp only [Guest.guestFn_te_new,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "te_new") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "te_new") (functionsHOL (declarations.drop 909)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "te_new") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_teNew_lookup

theorem originalRuntimeCode_msgNew_lookup :
    originalRuntimeCode.lookup (ofString "msg_new") =
      some ([],sourceFunctionBody Guest.guestFn_msg_new,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "msg_new") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "msg_new") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "msg_new")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 468 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original468 :: declarations.drop 469 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 469)).reverse).all
          (fun entry => !((ofString "msg_new") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original468 :: declarations.drop 469) =
          (ofString "msg_new",[],sourceFunctionBody Guest.guestFn_msg_new,ShapeHOL.one) ::
            functionsHOL (declarations.drop 469) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original468_eq]
        simp only [Guest.guestFn_msg_new,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "msg_new") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "msg_new") (functionsHOL (declarations.drop 469)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "msg_new") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_msgNew_lookup

theorem originalRuntimeCode_txHasAccessList_lookup :
    originalRuntimeCode.lookup (ofString "tx_has_access_list") =
      some ([(ofString "tx",.one)],sourceFunctionBody Guest.guestFn_tx_has_access_list,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "tx_has_access_list") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "tx_has_access_list") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "tx_has_access_list")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 318 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original318 :: declarations.drop 319 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 319)).reverse).all
          (fun entry => !((ofString "tx_has_access_list") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original318 :: declarations.drop 319) =
          (ofString "tx_has_access_list",[(ofString "tx",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_tx_has_access_list,ShapeHOL.one) ::
            functionsHOL (declarations.drop 319) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original318_eq]
        simp only [Guest.guestFn_tx_has_access_list,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "tx_has_access_list") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "tx_has_access_list") (functionsHOL (declarations.drop 319)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "tx_has_access_list") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_txHasAccessList_lookup

theorem originalRuntimeCode_txIsSetcode_lookup :
    originalRuntimeCode.lookup (ofString "tx_is_setcode") =
      some ([(ofString "tx",.one)],sourceFunctionBody Guest.guestFn_tx_is_setcode,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "tx_is_setcode") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "tx_is_setcode") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "tx_is_setcode")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 905 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original905 :: declarations.drop 906 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 906)).reverse).all
          (fun entry => !((ofString "tx_is_setcode") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original905 :: declarations.drop 906) =
          (ofString "tx_is_setcode",[(ofString "tx",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_tx_is_setcode,ShapeHOL.one) ::
            functionsHOL (declarations.drop 906) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original905_eq]
        simp only [Guest.guestFn_tx_is_setcode,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "tx_is_setcode") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "tx_is_setcode") (functionsHOL (declarations.drop 906)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "tx_is_setcode") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_txIsSetcode_lookup

theorem originalRuntimeCode_computeContractAddress_lookup :
    originalRuntimeCode.lookup (ofString "compute_contract_address") =
      some ([(ofString "addr",.one),(ofString "nonce",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_compute_contract_address,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "compute_contract_address") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "compute_contract_address") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "compute_contract_address")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 599 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original599 :: declarations.drop 600 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 600)).reverse).all
          (fun entry => !((ofString "compute_contract_address") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original599 :: declarations.drop 600) =
          (ofString "compute_contract_address",[(ofString "addr",ShapeHOL.one),(ofString "nonce",ShapeHOL.one),(ofString "out",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_compute_contract_address,ShapeHOL.one) ::
            functionsHOL (declarations.drop 600) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original599_eq]
        simp only [Guest.guestFn_compute_contract_address,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "compute_contract_address") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "compute_contract_address") (functionsHOL (declarations.drop 600)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "compute_contract_address") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_computeContractAddress_lookup

end InitECandidate.Runtime
