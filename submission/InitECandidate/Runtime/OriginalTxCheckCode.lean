import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_wsGetCode_lookup :
    originalRuntimeCode.lookup (ofString "ws_get_code") =
      some ([(ofString "code_hash",.one)],sourceFunctionBody Guest.guestFn_ws_get_code,(.comb [.one,.one])) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "ws_get_code") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "ws_get_code") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "ws_get_code")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 373 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original373 :: declarations.drop 374 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 374)).reverse).all
          (fun entry => !((ofString "ws_get_code") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original373 :: declarations.drop 374) =
          (ofString "ws_get_code",[(ofString "code_hash",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_ws_get_code,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 374) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original373_eq]
        simp only [Guest.guestFn_ws_get_code,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "ws_get_code") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "ws_get_code") (functionsHOL (declarations.drop 374)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "ws_get_code") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_wsGetCode_lookup

theorem originalRuntimeCode_getCode_lookup :
    originalRuntimeCode.lookup (ofString "get_code") =
      some ([(ofString "code_hash",.one),(ofString "addr",.one)],sourceFunctionBody Guest.guestFn_get_code,(.comb [.one,.one])) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "get_code") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "get_code") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "get_code")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 379 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original379 :: declarations.drop 380 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 380)).reverse).all
          (fun entry => !((ofString "get_code") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original379 :: declarations.drop 380) =
          (ofString "get_code",[(ofString "code_hash",ShapeHOL.one),(ofString "addr",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_get_code,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 380) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original379_eq]
        simp only [Guest.guestFn_get_code,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "get_code") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "get_code") (functionsHOL (declarations.drop 380)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "get_code") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_getCode_lookup

theorem originalRuntimeCode_blobGasPrice_lookup :
    originalRuntimeCode.lookup (ofString "calculate_blob_gas_price") =
      some ([(ofString "excess_blob_gas",.one)],sourceFunctionBody Guest.guestFn_calculate_blob_gas_price,(.comb [.one,.one,.one,.one])) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "calculate_blob_gas_price") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "calculate_blob_gas_price") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "calculate_blob_gas_price")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 236 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original236 :: declarations.drop 237 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 237)).reverse).all
          (fun entry => !((ofString "calculate_blob_gas_price") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original236 :: declarations.drop 237) =
          (ofString "calculate_blob_gas_price",[(ofString "excess_blob_gas",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_calculate_blob_gas_price,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 237) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original236_eq]
        simp only [Guest.guestFn_calculate_blob_gas_price,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "calculate_blob_gas_price") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "calculate_blob_gas_price") (functionsHOL (declarations.drop 237)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "calculate_blob_gas_price") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_blobGasPrice_lookup

theorem originalRuntimeCode_checkTransaction_lookup :
    originalRuntimeCode.lookup (ofString "check_transaction") =
      some ([(ofString "tx",.one),(ofString "sender",.one)],sourceFunctionBody Guest.guestFn_check_transaction,(.comb [.one,.one,.one,.one])) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "check_transaction") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "check_transaction") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "check_transaction")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 911 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original911 :: declarations.drop 912 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 912)).reverse).all
          (fun entry => !((ofString "check_transaction") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original911 :: declarations.drop 912) =
          (ofString "check_transaction",[(ofString "tx",ShapeHOL.one),(ofString "sender",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_check_transaction,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 912) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original911_eq]
        simp only [Guest.guestFn_check_transaction,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "check_transaction") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "check_transaction") (functionsHOL (declarations.drop 912)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "check_transaction") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_checkTransaction_lookup

end InitECandidate.Runtime
