import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_createEther_lookup :
    originalRuntimeCode.lookup (ofString "create_ether") =
      some ([(ofString "addr",.one),(ofString "amount",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_create_ether,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "create_ether") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "create_ether") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "create_ether")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 399 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original399 :: declarations.drop 400 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 400)).reverse).all
          (fun entry => !((ofString "create_ether") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original399 :: declarations.drop 400) =
          (ofString "create_ether",[(ofString "addr",ShapeHOL.one),(ofString "amount",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_create_ether,ShapeHOL.one) ::
            functionsHOL (declarations.drop 400) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original399_eq]
        simp only [Guest.guestFn_create_ether,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "create_ether") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "create_ether") (functionsHOL (declarations.drop 400)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "create_ether") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_createEther_lookup

theorem originalRuntimeCode_udivSmall5_lookup :
    originalRuntimeCode.lookup (ofString "udiv_small5") =
      some ([(ofString "x",.one)],sourceFunctionBody Guest.guestFn_udiv_small5,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "udiv_small5") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "udiv_small5") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "udiv_small5")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 913 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original913 :: declarations.drop 914 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 914)).reverse).all
          (fun entry => !((ofString "udiv_small5") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original913 :: declarations.drop 914) =
          (ofString "udiv_small5",[(ofString "x",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_udiv_small5,ShapeHOL.one) ::
            functionsHOL (declarations.drop 914) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original913_eq]
        simp only [Guest.guestFn_udiv_small5,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "udiv_small5") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "udiv_small5") (functionsHOL (declarations.drop 914)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "udiv_small5") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_udivSmall5_lookup

theorem originalRuntimeCode_lstNew_lookup :
    originalRuntimeCode.lookup (ofString "lst_new") =
      some ([(ofString "esz",.one),(ofString "cap",.one)],sourceFunctionBody Guest.guestFn_lst_new,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "lst_new") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "lst_new") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "lst_new")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 411 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original411 :: declarations.drop 412 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 412)).reverse).all
          (fun entry => !((ofString "lst_new") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original411 :: declarations.drop 412) =
          (ofString "lst_new",[(ofString "esz",ShapeHOL.one),(ofString "cap",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_lst_new,ShapeHOL.one) ::
            functionsHOL (declarations.drop 412) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original411_eq]
        simp only [Guest.guestFn_lst_new,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "lst_new") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "lst_new") (functionsHOL (declarations.drop 412)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "lst_new") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_lstNew_lookup

theorem originalRuntimeCode_lstPush_lookup :
    originalRuntimeCode.lookup (ofString "lst_push") =
      some ([(ofString "l",.one),(ofString "esz",.one)],sourceFunctionBody Guest.guestFn_lst_push,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "lst_push") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "lst_push") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "lst_push")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 413 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original413 :: declarations.drop 414 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 414)).reverse).all
          (fun entry => !((ofString "lst_push") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original413 :: declarations.drop 414) =
          (ofString "lst_push",[(ofString "l",ShapeHOL.one),(ofString "esz",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_lst_push,ShapeHOL.one) ::
            functionsHOL (declarations.drop 414) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original413_eq]
        simp only [Guest.guestFn_lst_push,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "lst_push") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "lst_push") (functionsHOL (declarations.drop 414)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "lst_push") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_lstPush_lookup

theorem originalRuntimeCode_encodeReceipt_lookup :
    originalRuntimeCode.lookup (ofString "encode_receipt") =
      some ([(ofString "tx_type",.one),(ofString "succeeded",.one),(ofString "cumulative_gas",.one),(ofString "logs",.one)],sourceFunctionBody Guest.guestFn_encode_receipt,(.comb [.one,.one])) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "encode_receipt") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "encode_receipt") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "encode_receipt")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 875 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original875 :: declarations.drop 876 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 876)).reverse).all
          (fun entry => !((ofString "encode_receipt") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original875 :: declarations.drop 876) =
          (ofString "encode_receipt",[(ofString "tx_type",ShapeHOL.one),(ofString "succeeded",ShapeHOL.one),(ofString "cumulative_gas",ShapeHOL.one),(ofString "logs",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_encode_receipt,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 876) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original875_eq]
        simp only [Guest.guestFn_encode_receipt,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "encode_receipt") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "encode_receipt") (functionsHOL (declarations.drop 876)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "encode_receipt") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_encodeReceipt_lookup

theorem originalRuntimeCode_incorporateTx_lookup :
    originalRuntimeCode.lookup (ofString "incorporate_tx_into_block") =
      some ([],sourceFunctionBody Guest.guestFn_incorporate_tx_into_block,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "incorporate_tx_into_block") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "incorporate_tx_into_block") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "incorporate_tx_into_block")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 431 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original431 :: declarations.drop 432 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 432)).reverse).all
          (fun entry => !((ofString "incorporate_tx_into_block") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original431 :: declarations.drop 432) =
          (ofString "incorporate_tx_into_block",[],sourceFunctionBody Guest.guestFn_incorporate_tx_into_block,ShapeHOL.one) ::
            functionsHOL (declarations.drop 432) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original431_eq]
        simp only [Guest.guestFn_incorporate_tx_into_block,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "incorporate_tx_into_block") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "incorporate_tx_into_block") (functionsHOL (declarations.drop 432)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "incorporate_tx_into_block") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_incorporateTx_lookup

theorem originalRuntimeCode_clearAccountPB_lookup :
    originalRuntimeCode.lookup (ofString "clear_account_preserving_balance") =
      some ([(ofString "addr",.one)],sourceFunctionBody Guest.guestFn_clear_account_preserving_balance,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "clear_account_preserving_balance") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "clear_account_preserving_balance") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "clear_account_preserving_balance")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 395 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original395 :: declarations.drop 396 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 396)).reverse).all
          (fun entry => !((ofString "clear_account_preserving_balance") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original395 :: declarations.drop 396) =
          (ofString "clear_account_preserving_balance",[(ofString "addr",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_clear_account_preserving_balance,ShapeHOL.one) ::
            functionsHOL (declarations.drop 396) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original395_eq]
        simp only [Guest.guestFn_clear_account_preserving_balance,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "clear_account_preserving_balance") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "clear_account_preserving_balance") (functionsHOL (declarations.drop 396)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "clear_account_preserving_balance") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_clearAccountPB_lookup

theorem originalRuntimeCode_htabItem_lookup :
    originalRuntimeCode.lookup (ofString "htab_item") =
      some ([(ofString "t",.one),(ofString "ordinal",.one)],sourceFunctionBody Guest.guestFn_htab_item,(.comb [.one,.one,.one])) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "htab_item") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "htab_item") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "htab_item")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 143 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original143 :: declarations.drop 144 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 144)).reverse).all
          (fun entry => !((ofString "htab_item") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original143 :: declarations.drop 144) =
          (ofString "htab_item",[(ofString "t",ShapeHOL.one),(ofString "ordinal",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_htab_item,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 144) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original143_eq]
        simp only [Guest.guestFn_htab_item,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "htab_item") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "htab_item") (functionsHOL (declarations.drop 144)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "htab_item") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_htabItem_lookup

theorem originalRuntimeCode_frameMemRelease_lookup :
    originalRuntimeCode.lookup (ofString "frame_mem_release") =
      some ([(ofString "m",.one)],sourceFunctionBody Guest.guestFn_frame_mem_release,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "frame_mem_release") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "frame_mem_release") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "frame_mem_release")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 13 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original13 :: declarations.drop 14 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 14)).reverse).all
          (fun entry => !((ofString "frame_mem_release") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original13 :: declarations.drop 14) =
          (ofString "frame_mem_release",[(ofString "m",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_frame_mem_release,ShapeHOL.one) ::
            functionsHOL (declarations.drop 14) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original13_eq]
        simp only [Guest.guestFn_frame_mem_release,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "frame_mem_release") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "frame_mem_release") (functionsHOL (declarations.drop 14)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "frame_mem_release") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_frameMemRelease_lookup

theorem originalRuntimeCode_max_lookup :
    originalRuntimeCode.lookup (ofString "max") =
      some ([(ofString "a",.one),(ofString "b",.one)],sourceFunctionBody Guest.guestFn_max,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "max") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "max") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "max")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 33 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original33 :: declarations.drop 34 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 34)).reverse).all
          (fun entry => !((ofString "max") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original33 :: declarations.drop 34) =
          (ofString "max",[(ofString "a",ShapeHOL.one),(ofString "b",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_max,ShapeHOL.one) ::
            functionsHOL (declarations.drop 34) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original33_eq]
        simp only [Guest.guestFn_max,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "max") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "max") (functionsHOL (declarations.drop 34)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "max") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_max_lookup

end InitECandidate.Runtime
