import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_senderAddressFromPublicKey_lookup :
    originalRuntimeCode.lookup (ofString "sender_address_from_public_key") =
      some ([(ofString "pubkey65",.one),(ofString "out20",.one)],sourceFunctionBody Guest.guestFn_sender_address_from_public_key,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "sender_address_from_public_key") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "sender_address_from_public_key") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "sender_address_from_public_key")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 344 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original344 :: declarations.drop 345 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 345)).reverse).all
          (fun entry => !((ofString "sender_address_from_public_key") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original344 :: declarations.drop 345) =
          (ofString "sender_address_from_public_key",[(ofString "pubkey65",ShapeHOL.one),(ofString "out20",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_sender_address_from_public_key,ShapeHOL.one) ::
            functionsHOL (declarations.drop 345) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original344_eq]
        simp only [Guest.guestFn_sender_address_from_public_key,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "sender_address_from_public_key") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "sender_address_from_public_key") (functionsHOL (declarations.drop 345)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "sender_address_from_public_key") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_senderAddressFromPublicKey_lookup

theorem originalRuntimeCode_recoverTransactionPublicKey_lookup :
    originalRuntimeCode.lookup (ofString "recover_transaction_public_key") =
      some ([(ofString "tx",.one),(ofString "chain_id",.one),(ofString "out64",.one)],sourceFunctionBody Guest.guestFn_recover_transaction_public_key,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "recover_transaction_public_key") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "recover_transaction_public_key") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "recover_transaction_public_key")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 343 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original343 :: declarations.drop 344 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 344)).reverse).all
          (fun entry => !((ofString "recover_transaction_public_key") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original343 :: declarations.drop 344) =
          (ofString "recover_transaction_public_key",[(ofString "tx",ShapeHOL.one),(ofString "chain_id",ShapeHOL.one),(ofString "out64",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_recover_transaction_public_key,ShapeHOL.one) ::
            functionsHOL (declarations.drop 344) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original343_eq]
        simp only [Guest.guestFn_recover_transaction_public_key,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "recover_transaction_public_key") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "recover_transaction_public_key") (functionsHOL (declarations.drop 344)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "recover_transaction_public_key") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_recoverTransactionPublicKey_lookup

theorem originalRuntimeCode_signatureRecoveryParameters_lookup :
    originalRuntimeCode.lookup (ofString "signature_recovery_parameters") =
      some ([(ofString "tx",.one),(ofString "chain_id",.one),(ofString "out_hash",.one)],sourceFunctionBody Guest.guestFn_signature_recovery_parameters,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "signature_recovery_parameters") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "signature_recovery_parameters") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "signature_recovery_parameters")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 342 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original342 :: declarations.drop 343 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 343)).reverse).all
          (fun entry => !((ofString "signature_recovery_parameters") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original342 :: declarations.drop 343) =
          (ofString "signature_recovery_parameters",[(ofString "tx",ShapeHOL.one),(ofString "chain_id",ShapeHOL.one),(ofString "out_hash",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_signature_recovery_parameters,ShapeHOL.one) ::
            functionsHOL (declarations.drop 343) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original342_eq]
        simp only [Guest.guestFn_signature_recovery_parameters,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "signature_recovery_parameters") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "signature_recovery_parameters") (functionsHOL (declarations.drop 343)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "signature_recovery_parameters") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_signatureRecoveryParameters_lookup

theorem originalRuntimeCode_signingHashPre155_lookup :
    originalRuntimeCode.lookup (ofString "signing_hash_pre155") =
      some ([(ofString "tx",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_signing_hash_pre155,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "signing_hash_pre155") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "signing_hash_pre155") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "signing_hash_pre155")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 335 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original335 :: declarations.drop 336 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 336)).reverse).all
          (fun entry => !((ofString "signing_hash_pre155") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original335 :: declarations.drop 336) =
          (ofString "signing_hash_pre155",[(ofString "tx",ShapeHOL.one),(ofString "out",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_signing_hash_pre155,ShapeHOL.one) ::
            functionsHOL (declarations.drop 336) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original335_eq]
        simp only [Guest.guestFn_signing_hash_pre155,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "signing_hash_pre155") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "signing_hash_pre155") (functionsHOL (declarations.drop 336)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "signing_hash_pre155") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_signingHashPre155_lookup

theorem originalRuntimeCode_txSigningHashMode_lookup :
    originalRuntimeCode.lookup (ofString "tx_signing_hash_mode") =
      some ([(ofString "tx",.one),(ofString "mode",.one),(ofString "chain_id",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_tx_signing_hash_mode,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "tx_signing_hash_mode") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "tx_signing_hash_mode") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "tx_signing_hash_mode")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 334 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original334 :: declarations.drop 335 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 335)).reverse).all
          (fun entry => !((ofString "tx_signing_hash_mode") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original334 :: declarations.drop 335) =
          (ofString "tx_signing_hash_mode",[(ofString "tx",ShapeHOL.one),(ofString "mode",ShapeHOL.one),(ofString "chain_id",ShapeHOL.one),(ofString "out",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_tx_signing_hash_mode,ShapeHOL.one) ::
            functionsHOL (declarations.drop 335) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original334_eq]
        simp only [Guest.guestFn_tx_signing_hash_mode,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "tx_signing_hash_mode") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "tx_signing_hash_mode") (functionsHOL (declarations.drop 335)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "tx_signing_hash_mode") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_txSigningHashMode_lookup

theorem originalRuntimeCode_signingHash7702_lookup :
    originalRuntimeCode.lookup (ofString "signing_hash_7702") =
      some ([(ofString "tx",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_signing_hash_7702,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "signing_hash_7702") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "signing_hash_7702") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "signing_hash_7702")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 340 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original340 :: declarations.drop 341 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 341)).reverse).all
          (fun entry => !((ofString "signing_hash_7702") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original340 :: declarations.drop 341) =
          (ofString "signing_hash_7702",[(ofString "tx",ShapeHOL.one),(ofString "out",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_signing_hash_7702,ShapeHOL.one) ::
            functionsHOL (declarations.drop 341) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original340_eq]
        simp only [Guest.guestFn_signing_hash_7702,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "signing_hash_7702") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "signing_hash_7702") (functionsHOL (declarations.drop 341)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "signing_hash_7702") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_signingHash7702_lookup

theorem originalRuntimeCode_signingHash4844_lookup :
    originalRuntimeCode.lookup (ofString "signing_hash_4844") =
      some ([(ofString "tx",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_signing_hash_4844,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "signing_hash_4844") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "signing_hash_4844") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "signing_hash_4844")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 339 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original339 :: declarations.drop 340 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 340)).reverse).all
          (fun entry => !((ofString "signing_hash_4844") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original339 :: declarations.drop 340) =
          (ofString "signing_hash_4844",[(ofString "tx",ShapeHOL.one),(ofString "out",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_signing_hash_4844,ShapeHOL.one) ::
            functionsHOL (declarations.drop 340) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original339_eq]
        simp only [Guest.guestFn_signing_hash_4844,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "signing_hash_4844") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "signing_hash_4844") (functionsHOL (declarations.drop 340)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "signing_hash_4844") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_signingHash4844_lookup

theorem originalRuntimeCode_signingHash2930_lookup :
    originalRuntimeCode.lookup (ofString "signing_hash_2930") =
      some ([(ofString "tx",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_signing_hash_2930,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "signing_hash_2930") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "signing_hash_2930") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "signing_hash_2930")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 337 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original337 :: declarations.drop 338 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 338)).reverse).all
          (fun entry => !((ofString "signing_hash_2930") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original337 :: declarations.drop 338) =
          (ofString "signing_hash_2930",[(ofString "tx",ShapeHOL.one),(ofString "out",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_signing_hash_2930,ShapeHOL.one) ::
            functionsHOL (declarations.drop 338) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original337_eq]
        simp only [Guest.guestFn_signing_hash_2930,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "signing_hash_2930") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "signing_hash_2930") (functionsHOL (declarations.drop 338)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "signing_hash_2930") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_signingHash2930_lookup

theorem originalRuntimeCode_signingHash1559_lookup :
    originalRuntimeCode.lookup (ofString "signing_hash_1559") =
      some ([(ofString "tx",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_signing_hash_1559,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "signing_hash_1559") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "signing_hash_1559") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "signing_hash_1559")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 338 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original338 :: declarations.drop 339 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 339)).reverse).all
          (fun entry => !((ofString "signing_hash_1559") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original338 :: declarations.drop 339) =
          (ofString "signing_hash_1559",[(ofString "tx",ShapeHOL.one),(ofString "out",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_signing_hash_1559,ShapeHOL.one) ::
            functionsHOL (declarations.drop 339) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original338_eq]
        simp only [Guest.guestFn_signing_hash_1559,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "signing_hash_1559") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "signing_hash_1559") (functionsHOL (declarations.drop 339)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "signing_hash_1559") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_signingHash1559_lookup

theorem originalRuntimeCode_signingHash155_lookup :
    originalRuntimeCode.lookup (ofString "signing_hash_155") =
      some ([(ofString "tx",.one),(ofString "chain_id",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_signing_hash_155,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "signing_hash_155") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "signing_hash_155") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "signing_hash_155")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 336 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original336 :: declarations.drop 337 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 337)).reverse).all
          (fun entry => !((ofString "signing_hash_155") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original336 :: declarations.drop 337) =
          (ofString "signing_hash_155",[(ofString "tx",ShapeHOL.one),(ofString "chain_id",ShapeHOL.one),(ofString "out",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_signing_hash_155,ShapeHOL.one) ::
            functionsHOL (declarations.drop 337) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original336_eq]
        simp only [Guest.guestFn_signing_hash_155,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "signing_hash_155") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "signing_hash_155") (functionsHOL (declarations.drop 337)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "signing_hash_155") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_signingHash155_lookup

theorem originalRuntimeCode_secp256k1Recover_lookup :
    originalRuntimeCode.lookup (ofString "secp256k1_recover") =
      some ([(ofString "msg_hash",.one),(ofString "r",.comb [.one,.one,.one,.one]),(ofString "s",.comb [.one,.one,.one,.one]),(ofString "recid",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_secp256k1_recover,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "secp256k1_recover") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "secp256k1_recover") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "secp256k1_recover")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 185 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original185 :: declarations.drop 186 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 186)).reverse).all
          (fun entry => !((ofString "secp256k1_recover") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original185 :: declarations.drop 186) =
          (ofString "secp256k1_recover",[(ofString "msg_hash",ShapeHOL.one),(ofString "r",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "s",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "recid",ShapeHOL.one),(ofString "out",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_secp256k1_recover,ShapeHOL.one) ::
            functionsHOL (declarations.drop 186) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original185_eq]
        simp only [Guest.guestFn_secp256k1_recover,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "secp256k1_recover") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "secp256k1_recover") (functionsHOL (declarations.drop 186)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "secp256k1_recover") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_secp256k1Recover_lookup

theorem originalRuntimeCode_secp256k1DecompressR_lookup :
    originalRuntimeCode.lookup (ofString "secp256k1_decompress_r") =
      some ([(ofString "r",.comb [.one,.one,.one,.one]),(ofString "recid",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_secp256k1_decompress_r,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "secp256k1_decompress_r") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "secp256k1_decompress_r") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "secp256k1_decompress_r")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 184 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original184 :: declarations.drop 185 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 185)).reverse).all
          (fun entry => !((ofString "secp256k1_decompress_r") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original184 :: declarations.drop 185) =
          (ofString "secp256k1_decompress_r",[(ofString "r",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "recid",ShapeHOL.one),(ofString "out",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_secp256k1_decompress_r,ShapeHOL.one) ::
            functionsHOL (declarations.drop 185) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original184_eq]
        simp only [Guest.guestFn_secp256k1_decompress_r,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "secp256k1_decompress_r") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "secp256k1_decompress_r") (functionsHOL (declarations.drop 185)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "secp256k1_decompress_r") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_secp256k1DecompressR_lookup

theorem originalRuntimeCode_fpSqrt_lookup :
    originalRuntimeCode.lookup (ofString "fp_sqrt") =
      some ([(ofString "a",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_fp_sqrt,(.comb [.one,.one,.one,.one])) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "fp_sqrt") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "fp_sqrt") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "fp_sqrt")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 166 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original166 :: declarations.drop 167 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 167)).reverse).all
          (fun entry => !((ofString "fp_sqrt") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original166 :: declarations.drop 167) =
          (ofString "fp_sqrt",[(ofString "a",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_fp_sqrt,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 167) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original166_eq]
        simp only [Guest.guestFn_fp_sqrt,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "fp_sqrt") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "fp_sqrt") (functionsHOL (declarations.drop 167)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "fp_sqrt") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_fpSqrt_lookup

theorem originalRuntimeCode_secpAccelFpPow4_lookup :
    originalRuntimeCode.lookup (ofString "secp_accel_fp_pow4") =
      some ([(ofString "a",.comb [.one,.one,.one,.one]),(ofString "e",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_secp_accel_fp_pow4,(.comb [.one,.one,.one,.one])) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "secp_accel_fp_pow4") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "secp_accel_fp_pow4") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "secp_accel_fp_pow4")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 159 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original159 :: declarations.drop 160 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 160)).reverse).all
          (fun entry => !((ofString "secp_accel_fp_pow4") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original159 :: declarations.drop 160) =
          (ofString "secp_accel_fp_pow4",[(ofString "a",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "e",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_secp_accel_fp_pow4,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 160) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original159_eq]
        simp only [Guest.guestFn_secp_accel_fp_pow4,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "secp_accel_fp_pow4") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "secp_accel_fp_pow4") (functionsHOL (declarations.drop 160)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "secp_accel_fp_pow4") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_secpAccelFpPow4_lookup

theorem originalRuntimeCode_fnInv_lookup :
    originalRuntimeCode.lookup (ofString "fn_inv") =
      some ([(ofString "a",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_fn_inv,(.comb [.one,.one,.one,.one])) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "fn_inv") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "fn_inv") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "fn_inv")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 172 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original172 :: declarations.drop 173 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 173)).reverse).all
          (fun entry => !((ofString "fn_inv") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original172 :: declarations.drop 173) =
          (ofString "fn_inv",[(ofString "a",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_fn_inv,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 173) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original172_eq]
        simp only [Guest.guestFn_fn_inv,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "fn_inv") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "fn_inv") (functionsHOL (declarations.drop 173)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "fn_inv") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_fnInv_lookup

theorem originalRuntimeCode_secpAccelFnPow4_lookup :
    originalRuntimeCode.lookup (ofString "secp_accel_fn_pow4") =
      some ([(ofString "a",.comb [.one,.one,.one,.one]),(ofString "e",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_secp_accel_fn_pow4,(.comb [.one,.one,.one,.one])) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "secp_accel_fn_pow4") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "secp_accel_fn_pow4") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "secp_accel_fn_pow4")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 169 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original169 :: declarations.drop 170 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 170)).reverse).all
          (fun entry => !((ofString "secp_accel_fn_pow4") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original169 :: declarations.drop 170) =
          (ofString "secp_accel_fn_pow4",[(ofString "a",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "e",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_secp_accel_fn_pow4,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 170) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original169_eq]
        simp only [Guest.guestFn_secp_accel_fn_pow4,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "secp_accel_fn_pow4") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "secp_accel_fn_pow4") (functionsHOL (declarations.drop 170)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "secp_accel_fn_pow4") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_secpAccelFnPow4_lookup

theorem originalRuntimeCode_ecToAffine_lookup :
    originalRuntimeCode.lookup (ofString "ec_to_affine") =
      some ([(ofString "pt",.one)],sourceFunctionBody Guest.guestFn_ec_to_affine,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "ec_to_affine") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "ec_to_affine") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "ec_to_affine")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 182 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original182 :: declarations.drop 183 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 183)).reverse).all
          (fun entry => !((ofString "ec_to_affine") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original182 :: declarations.drop 183) =
          (ofString "ec_to_affine",[(ofString "pt",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_ec_to_affine,ShapeHOL.one) ::
            functionsHOL (declarations.drop 183) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original182_eq]
        simp only [Guest.guestFn_ec_to_affine,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "ec_to_affine") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "ec_to_affine") (functionsHOL (declarations.drop 183)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "ec_to_affine") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_ecToAffine_lookup

theorem originalRuntimeCode_fpInv_lookup :
    originalRuntimeCode.lookup (ofString "fp_inv") =
      some ([(ofString "a",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_fp_inv,(.comb [.one,.one,.one,.one])) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "fp_inv") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "fp_inv") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "fp_inv")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 165 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original165 :: declarations.drop 166 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 166)).reverse).all
          (fun entry => !((ofString "fp_inv") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original165 :: declarations.drop 166) =
          (ofString "fp_inv",[(ofString "a",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_fp_inv,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 166) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original165_eq]
        simp only [Guest.guestFn_fp_inv,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "fp_inv") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "fp_inv") (functionsHOL (declarations.drop 166)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "fp_inv") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_fpInv_lookup

theorem originalRuntimeCode_ecMul2_lookup :
    originalRuntimeCode.lookup (ofString "ec_mul2") =
      some ([(ofString "out",.one),(ofString "k1",.comb [.one,.one,.one,.one]),(ofString "ax",.comb [.one,.one,.one,.one]),(ofString "ay",.comb [.one,.one,.one,.one]),(ofString "k2",.comb [.one,.one,.one,.one]),(ofString "bx",.comb [.one,.one,.one,.one]),(ofString "by",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_ec_mul2,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "ec_mul2") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "ec_mul2") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "ec_mul2")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 181 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original181 :: declarations.drop 182 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 182)).reverse).all
          (fun entry => !((ofString "ec_mul2") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original181 :: declarations.drop 182) =
          (ofString "ec_mul2",[(ofString "out",ShapeHOL.one),(ofString "k1",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "ax",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "ay",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "k2",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "bx",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "by",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_ec_mul2,ShapeHOL.one) ::
            functionsHOL (declarations.drop 182) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original181_eq]
        simp only [Guest.guestFn_ec_mul2,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "ec_mul2") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "ec_mul2") (functionsHOL (declarations.drop 182)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "ec_mul2") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_ecMul2_lookup

theorem originalRuntimeCode_ecDouble_lookup :
    originalRuntimeCode.lookup (ofString "ec_double") =
      some ([(ofString "pt",.one)],sourceFunctionBody Guest.guestFn_ec_double,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "ec_double") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "ec_double") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "ec_double")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 177 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original177 :: declarations.drop 178 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 178)).reverse).all
          (fun entry => !((ofString "ec_double") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original177 :: declarations.drop 178) =
          (ofString "ec_double",[(ofString "pt",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_ec_double,ShapeHOL.one) ::
            functionsHOL (declarations.drop 178) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original177_eq]
        simp only [Guest.guestFn_ec_double,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "ec_double") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "ec_double") (functionsHOL (declarations.drop 178)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "ec_double") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_ecDouble_lookup

theorem originalRuntimeCode_secpAccelNormalize_lookup :
    originalRuntimeCode.lookup (ofString "secp_accel_normalize") =
      some ([(ofString "pt",.one)],sourceFunctionBody Guest.guestFn_secp_accel_normalize,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "secp_accel_normalize") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "secp_accel_normalize") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "secp_accel_normalize")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 176 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original176 :: declarations.drop 177 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 177)).reverse).all
          (fun entry => !((ofString "secp_accel_normalize") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original176 :: declarations.drop 177) =
          (ofString "secp_accel_normalize",[(ofString "pt",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_secp_accel_normalize,ShapeHOL.one) ::
            functionsHOL (declarations.drop 177) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original176_eq]
        simp only [Guest.guestFn_secp_accel_normalize,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "secp_accel_normalize") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "secp_accel_normalize") (functionsHOL (declarations.drop 177)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "secp_accel_normalize") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_secpAccelNormalize_lookup

theorem originalRuntimeCode_ecAddAffine_lookup :
    originalRuntimeCode.lookup (ofString "ec_add_affine") =
      some ([(ofString "pt",.one),(ofString "ax",.comb [.one,.one,.one,.one]),(ofString "ay",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_ec_add_affine,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "ec_add_affine") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "ec_add_affine") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "ec_add_affine")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 178 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original178 :: declarations.drop 179 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 179)).reverse).all
          (fun entry => !((ofString "ec_add_affine") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original178 :: declarations.drop 179) =
          (ofString "ec_add_affine",[(ofString "pt",ShapeHOL.one),(ofString "ax",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "ay",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_ec_add_affine,ShapeHOL.one) ::
            functionsHOL (declarations.drop 179) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original178_eq]
        simp only [Guest.guestFn_ec_add_affine,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "ec_add_affine") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "ec_add_affine") (functionsHOL (declarations.drop 179)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "ec_add_affine") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_ecAddAffine_lookup

end InitECandidate.Runtime
