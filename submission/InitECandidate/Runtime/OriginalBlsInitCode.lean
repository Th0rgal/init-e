import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_blsConstsInit_lookup :
    originalRuntimeCode.lookup (ofString "bls_consts_init") =
      some ([],sourceFunctionBody Guest.guestFn_bls_consts_init,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "bls_consts_init") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "bls_consts_init") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "bls_consts_init")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 721 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original721 :: declarations.drop 722 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 722)).reverse).all
          (fun entry => !((ofString "bls_consts_init") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original721 :: declarations.drop 722) =
          (ofString "bls_consts_init",[],sourceFunctionBody Guest.guestFn_bls_consts_init,ShapeHOL.one) ::
            functionsHOL (declarations.drop 722) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original721_eq]
        simp only [Guest.guestFn_bls_consts_init,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "bls_consts_init") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "bls_consts_init") (functionsHOL (declarations.drop 722)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "bls_consts_init") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_blsConstsInit_lookup

theorem originalRuntimeCode_fpAccelInit_lookup :
    originalRuntimeCode.lookup (ofString "fp_accel_init") =
      some ([],sourceFunctionBody Guest.guestFn_fp_accel_init,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "fp_accel_init") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "fp_accel_init") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "fp_accel_init")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 736 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original736 :: declarations.drop 737 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 737)).reverse).all
          (fun entry => !((ofString "fp_accel_init") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original736 :: declarations.drop 737) =
          (ofString "fp_accel_init",[],sourceFunctionBody Guest.guestFn_fp_accel_init,ShapeHOL.one) ::
            functionsHOL (declarations.drop 737) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original736_eq]
        simp only [Guest.guestFn_fp_accel_init,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "fp_accel_init") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "fp_accel_init") (functionsHOL (declarations.drop 737)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "fp_accel_init") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_fpAccelInit_lookup

theorem originalRuntimeCode_fp2AccelInit_lookup :
    originalRuntimeCode.lookup (ofString "fp2_accel_init") =
      some ([],sourceFunctionBody Guest.guestFn_fp2_accel_init,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "fp2_accel_init") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "fp2_accel_init") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "fp2_accel_init")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 760 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original760 :: declarations.drop 761 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 761)).reverse).all
          (fun entry => !((ofString "fp2_accel_init") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original760 :: declarations.drop 761) =
          (ofString "fp2_accel_init",[],sourceFunctionBody Guest.guestFn_fp2_accel_init,ShapeHOL.one) ::
            functionsHOL (declarations.drop 761) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original760_eq]
        simp only [Guest.guestFn_fp2_accel_init,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "fp2_accel_init") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "fp2_accel_init") (functionsHOL (declarations.drop 761)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "fp2_accel_init") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_fp2AccelInit_lookup

theorem originalRuntimeCode_blsG1AccelInit_lookup :
    originalRuntimeCode.lookup (ofString "bls_g1_accel_init") =
      some ([],sourceFunctionBody Guest.guestFn_bls_g1_accel_init,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "bls_g1_accel_init") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "bls_g1_accel_init") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "bls_g1_accel_init")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 796 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original796 :: declarations.drop 797 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 797)).reverse).all
          (fun entry => !((ofString "bls_g1_accel_init") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original796 :: declarations.drop 797) =
          (ofString "bls_g1_accel_init",[],sourceFunctionBody Guest.guestFn_bls_g1_accel_init,ShapeHOL.one) ::
            functionsHOL (declarations.drop 797) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original796_eq]
        simp only [Guest.guestFn_bls_g1_accel_init,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "bls_g1_accel_init") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "bls_g1_accel_init") (functionsHOL (declarations.drop 797)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "bls_g1_accel_init") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_blsG1AccelInit_lookup

theorem originalRuntimeCode_blsLibInit_lookup :
    originalRuntimeCode.lookup (ofString "bls_lib_init") =
      some ([],sourceFunctionBody Guest.guestFn_bls_lib_init,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "bls_lib_init") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "bls_lib_init") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "bls_lib_init")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 840 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original840 :: declarations.drop 841 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 841)).reverse).all
          (fun entry => !((ofString "bls_lib_init") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original840 :: declarations.drop 841) =
          (ofString "bls_lib_init",[],sourceFunctionBody Guest.guestFn_bls_lib_init,ShapeHOL.one) ::
            functionsHOL (declarations.drop 841) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original840_eq]
        simp only [Guest.guestFn_bls_lib_init,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "bls_lib_init") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "bls_lib_init") (functionsHOL (declarations.drop 841)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "bls_lib_init") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_blsLibInit_lookup

theorem originalRuntimeCode_blsPrecompilesInit_lookup :
    originalRuntimeCode.lookup (ofString "bls_precompiles_init") =
      some ([],sourceFunctionBody Guest.guestFn_bls_precompiles_init,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "bls_precompiles_init") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "bls_precompiles_init") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "bls_precompiles_init")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 850 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original850 :: declarations.drop 851 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 851)).reverse).all
          (fun entry => !((ofString "bls_precompiles_init") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original850 :: declarations.drop 851) =
          (ofString "bls_precompiles_init",[],sourceFunctionBody Guest.guestFn_bls_precompiles_init,ShapeHOL.one) ::
            functionsHOL (declarations.drop 851) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original850_eq]
        simp only [Guest.guestFn_bls_precompiles_init,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "bls_precompiles_init") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "bls_precompiles_init") (functionsHOL (declarations.drop 851)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "bls_precompiles_init") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_blsPrecompilesInit_lookup

end InitECandidate.Runtime
