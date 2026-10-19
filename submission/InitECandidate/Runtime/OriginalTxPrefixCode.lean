import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_totalBlobGas_lookup :
    originalRuntimeCode.lookup (ofString "calculate_total_blob_gas") =
      some ([(ofString "tx",.one)],sourceFunctionBody Guest.guestFn_calculate_total_blob_gas,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "calculate_total_blob_gas") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "calculate_total_blob_gas") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "calculate_total_blob_gas")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 320 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original320 :: declarations.drop 321 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 321)).reverse).all
          (fun entry => !((ofString "calculate_total_blob_gas") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original320 :: declarations.drop 321) =
          (ofString "calculate_total_blob_gas",[(ofString "tx",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_calculate_total_blob_gas,ShapeHOL.one) ::
            functionsHOL (declarations.drop 321) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original320_eq]
        simp only [Guest.guestFn_calculate_total_blob_gas,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "calculate_total_blob_gas") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "calculate_total_blob_gas") (functionsHOL (declarations.drop 321)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "calculate_total_blob_gas") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_totalBlobGas_lookup

theorem originalRuntimeCode_encodeTransaction_lookup :
    originalRuntimeCode.lookup (ofString "encode_transaction") =
      some ([(ofString "tx",.one)],sourceFunctionBody Guest.guestFn_encode_transaction,(.comb [.one,.one])) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "encode_transaction") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "encode_transaction") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "encode_transaction")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 332 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original332 :: declarations.drop 333 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 333)).reverse).all
          (fun entry => !((ofString "encode_transaction") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original332 :: declarations.drop 333) =
          (ofString "encode_transaction",[(ofString "tx",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_encode_transaction,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 333) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original332_eq]
        simp only [Guest.guestFn_encode_transaction,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "encode_transaction") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "encode_transaction") (functionsHOL (declarations.drop 333)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "encode_transaction") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_encodeTransaction_lookup

theorem originalRuntimeCode_txChainId_lookup :
    originalRuntimeCode.lookup (ofString "tx_chain_id") =
      some ([(ofString "tx",.one)],sourceFunctionBody Guest.guestFn_tx_chain_id,(.comb [.one,.one])) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "tx_chain_id") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "tx_chain_id") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "tx_chain_id")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 341 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original341 :: declarations.drop 342 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 342)).reverse).all
          (fun entry => !((ofString "tx_chain_id") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original341 :: declarations.drop 342) =
          (ofString "tx_chain_id",[(ofString "tx",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_tx_chain_id,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 342) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original341_eq]
        simp only [Guest.guestFn_tx_chain_id,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "tx_chain_id") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "tx_chain_id") (functionsHOL (declarations.drop 342)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "tx_chain_id") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_txChainId_lookup

theorem originalRuntimeCode_recoverSender_lookup :
    originalRuntimeCode.lookup (ofString "recover_sender_with_chain_id") =
      some ([(ofString "tx",.one),(ofString "chain_id",.one),(ofString "out20",.one)],sourceFunctionBody Guest.guestFn_recover_sender_with_chain_id,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "recover_sender_with_chain_id") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "recover_sender_with_chain_id") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "recover_sender_with_chain_id")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 346 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original346 :: declarations.drop 347 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 347)).reverse).all
          (fun entry => !((ofString "recover_sender_with_chain_id") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original346 :: declarations.drop 347) =
          (ofString "recover_sender_with_chain_id",[(ofString "tx",ShapeHOL.one),(ofString "chain_id",ShapeHOL.one),(ofString "out20",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_recover_sender_with_chain_id,ShapeHOL.one) ::
            functionsHOL (declarations.drop 347) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original346_eq]
        simp only [Guest.guestFn_recover_sender_with_chain_id,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "recover_sender_with_chain_id") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "recover_sender_with_chain_id") (functionsHOL (declarations.drop 347)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "recover_sender_with_chain_id") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_recoverSender_lookup

theorem originalRuntimeCode_validateTransaction_lookup :
    originalRuntimeCode.lookup (ofString "validate_transaction") =
      some ([(ofString "tx",.one),(ofString "sender",.one)],sourceFunctionBody Guest.guestFn_validate_transaction,(.comb [.one,.one,.one])) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "validate_transaction") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "validate_transaction") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "validate_transaction")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 349 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original349 :: declarations.drop 350 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 350)).reverse).all
          (fun entry => !((ofString "validate_transaction") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original349 :: declarations.drop 350) =
          (ofString "validate_transaction",[(ofString "tx",ShapeHOL.one),(ofString "sender",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_validate_transaction,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 350) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original349_eq]
        simp only [Guest.guestFn_validate_transaction,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "validate_transaction") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "validate_transaction") (functionsHOL (declarations.drop 350)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "validate_transaction") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_validateTransaction_lookup

theorem originalRuntimeCode_feeMul_lookup :
    originalRuntimeCode.lookup (ofString "fee_mul") =
      some ([(ofString "gas",.one),(ofString "price",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_fee_mul,(.comb [.one,.one,.one,.one,.one])) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "fee_mul") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "fee_mul") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "fee_mul")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 906 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original906 :: declarations.drop 907 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 907)).reverse).all
          (fun entry => !((ofString "fee_mul") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original906 :: declarations.drop 907) =
          (ofString "fee_mul",[(ofString "gas",ShapeHOL.one),(ofString "price",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_fee_mul,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 907) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original906_eq]
        simp only [Guest.guestFn_fee_mul,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "fee_mul") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "fee_mul") (functionsHOL (declarations.drop 907)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "fee_mul") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_feeMul_lookup

end InitECandidate.Runtime
