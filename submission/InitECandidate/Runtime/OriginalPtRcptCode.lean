import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_rlpFinishList_lookup :
    originalRuntimeCode.lookup (ofString "rlp_finish_list") =
      some ([(ofString "dst",.one),(ofString "payload_end",.one)],sourceFunctionBody Guest.guestFn_rlp_finish_list,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "rlp_finish_list") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "rlp_finish_list") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "rlp_finish_list")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 872 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original872 :: declarations.drop 873 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 873)).reverse).all
          (fun entry => !((ofString "rlp_finish_list") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original872 :: declarations.drop 873) =
          (ofString "rlp_finish_list",[(ofString "dst",ShapeHOL.one),(ofString "payload_end",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_rlp_finish_list,ShapeHOL.one) ::
            functionsHOL (declarations.drop 873) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original872_eq]
        simp only [Guest.guestFn_rlp_finish_list,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "rlp_finish_list") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "rlp_finish_list") (functionsHOL (declarations.drop 873)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "rlp_finish_list") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_rlpFinishList_lookup

theorem originalRuntimeCode_encodeLogs_lookup :
    originalRuntimeCode.lookup (ofString "encode_logs") =
      some ([(ofString "dst",.one),(ofString "logs",.one)],sourceFunctionBody Guest.guestFn_encode_logs,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "encode_logs") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "encode_logs") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "encode_logs")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 874 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original874 :: declarations.drop 875 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 875)).reverse).all
          (fun entry => !((ofString "encode_logs") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original874 :: declarations.drop 875) =
          (ofString "encode_logs",[(ofString "dst",ShapeHOL.one),(ofString "logs",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_encode_logs,ShapeHOL.one) ::
            functionsHOL (declarations.drop 875) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original874_eq]
        simp only [Guest.guestFn_encode_logs,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "encode_logs") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "encode_logs") (functionsHOL (declarations.drop 875)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "encode_logs") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_encodeLogs_lookup

theorem originalRuntimeCode_logsBloom_lookup :
    originalRuntimeCode.lookup (ofString "logs_bloom") =
      some ([(ofString "logs",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_logs_bloom,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "logs_bloom") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "logs_bloom") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "logs_bloom")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 871 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original871 :: declarations.drop 872 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 872)).reverse).all
          (fun entry => !((ofString "logs_bloom") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original871 :: declarations.drop 872) =
          (ofString "logs_bloom",[(ofString "logs",ShapeHOL.one),(ofString "out",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_logs_bloom,ShapeHOL.one) ::
            functionsHOL (declarations.drop 872) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original871_eq]
        simp only [Guest.guestFn_logs_bloom,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "logs_bloom") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "logs_bloom") (functionsHOL (declarations.drop 872)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "logs_bloom") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_logsBloom_lookup

theorem originalRuntimeCode_addToBloom_lookup :
    originalRuntimeCode.lookup (ofString "add_to_bloom") =
      some ([(ofString "bloom",.one),(ofString "entry",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_add_to_bloom,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "add_to_bloom") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "add_to_bloom") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "add_to_bloom")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 870 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original870 :: declarations.drop 871 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 871)).reverse).all
          (fun entry => !((ofString "add_to_bloom") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original870 :: declarations.drop 871) =
          (ofString "add_to_bloom",[(ofString "bloom",ShapeHOL.one),(ofString "entry",ShapeHOL.one),(ofString "n",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_add_to_bloom,ShapeHOL.one) ::
            functionsHOL (declarations.drop 871) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original870_eq]
        simp only [Guest.guestFn_add_to_bloom,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "add_to_bloom") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "add_to_bloom") (functionsHOL (declarations.drop 871)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "add_to_bloom") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_addToBloom_lookup

theorem originalRuntimeCode_logsEncodedBound_lookup :
    originalRuntimeCode.lookup (ofString "logs_encoded_bound") =
      some ([(ofString "logs",.one)],sourceFunctionBody Guest.guestFn_logs_encoded_bound,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "logs_encoded_bound") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "logs_encoded_bound") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "logs_encoded_bound")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 873 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original873 :: declarations.drop 874 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 874)).reverse).all
          (fun entry => !((ofString "logs_encoded_bound") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original873 :: declarations.drop 874) =
          (ofString "logs_encoded_bound",[(ofString "logs",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_logs_encoded_bound,ShapeHOL.one) ::
            functionsHOL (declarations.drop 874) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original873_eq]
        simp only [Guest.guestFn_logs_encoded_bound,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "logs_encoded_bound") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "logs_encoded_bound") (functionsHOL (declarations.drop 874)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "logs_encoded_bound") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_logsEncodedBound_lookup

end InitECandidate.Runtime
