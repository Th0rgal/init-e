import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_bn254AccelInit_lookup :
    originalRuntimeCode.lookup (ofString "bn254_accel_init") =
      some ([],sourceFunctionBody Guest.guestFn_bn254_accel_init,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "bn254_accel_init") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "bn254_accel_init") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "bn254_accel_init")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 665 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original665 :: declarations.drop 666 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 666)).reverse).all
          (fun entry => !((ofString "bn254_accel_init") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original665 :: declarations.drop 666) =
          (ofString "bn254_accel_init",[],sourceFunctionBody Guest.guestFn_bn254_accel_init,ShapeHOL.one) ::
            functionsHOL (declarations.drop 666) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original665_eq]
        simp only [Guest.guestFn_bn254_accel_init,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "bn254_accel_init") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "bn254_accel_init") (functionsHOL (declarations.drop 666)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "bn254_accel_init") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_bn254AccelInit_lookup

theorem originalRuntimeCode_bn254AccelModmul_lookup :
    originalRuntimeCode.lookup (ofString "bn254_accel_modmul") =
      some ([(ofString "a",.comb [.one,.one,.one,.one]),(ofString "b",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_bn254_accel_modmul,.comb [.one,.one,.one,.one]) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "bn254_accel_modmul") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "bn254_accel_modmul") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "bn254_accel_modmul")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 666 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original666 :: declarations.drop 667 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 667)).reverse).all
          (fun entry => !((ofString "bn254_accel_modmul") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original666 :: declarations.drop 667) =
          (ofString "bn254_accel_modmul",[(ofString "a",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "b",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_bn254_accel_modmul,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 667) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original666_eq]
        simp only [Guest.guestFn_bn254_accel_modmul,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "bn254_accel_modmul") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "bn254_accel_modmul") (functionsHOL (declarations.drop 667)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "bn254_accel_modmul") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_bn254AccelModmul_lookup

theorem originalRuntimeCode_fqMul_lookup :
    originalRuntimeCode.lookup (ofString "fq_mul") =
      some ([(ofString "a",.comb [.one,.one,.one,.one]),(ofString "b",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_fq_mul,.comb [.one,.one,.one,.one]) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "fq_mul") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "fq_mul") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "fq_mul")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 675 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original675 :: declarations.drop 676 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 676)).reverse).all
          (fun entry => !((ofString "fq_mul") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original675 :: declarations.drop 676) =
          (ofString "fq_mul",[(ofString "a",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "b",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_fq_mul,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 676) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original675_eq]
        simp only [Guest.guestFn_fq_mul,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "fq_mul") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "fq_mul") (functionsHOL (declarations.drop 676)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "fq_mul") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_fqMul_lookup

theorem originalRuntimeCode_fqNeg_lookup :
    originalRuntimeCode.lookup (ofString "fq_neg") =
      some ([(ofString "a",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_fq_neg,.comb [.one,.one,.one,.one]) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "fq_neg") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "fq_neg") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "fq_neg")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 674 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original674 :: declarations.drop 675 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 675)).reverse).all
          (fun entry => !((ofString "fq_neg") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original674 :: declarations.drop 675) =
          (ofString "fq_neg",[(ofString "a",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_fq_neg,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 675) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original674_eq]
        simp only [Guest.guestFn_fq_neg,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "fq_neg") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "fq_neg") (functionsHOL (declarations.drop 675)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "fq_neg") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_fqNeg_lookup

theorem originalRuntimeCode_u256IsZero_lookup :
    originalRuntimeCode.lookup (ofString "u256_is_zero") =
      some ([(ofString "a",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_u256_is_zero,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "u256_is_zero") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "u256_is_zero") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "u256_is_zero")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 43 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original43 :: declarations.drop 44 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 44)).reverse).all
          (fun entry => !((ofString "u256_is_zero") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original43 :: declarations.drop 44) =
          (ofString "u256_is_zero",[(ofString "a",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_u256_is_zero,ShapeHOL.one) ::
            functionsHOL (declarations.drop 44) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original43_eq]
        simp only [Guest.guestFn_u256_is_zero,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "u256_is_zero") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "u256_is_zero") (functionsHOL (declarations.drop 44)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "u256_is_zero") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_u256IsZero_lookup

theorem originalRuntimeCode_u256Sub_lookup :
    originalRuntimeCode.lookup (ofString "u256_sub") =
      some ([(ofString "a",.comb [.one,.one,.one,.one]),(ofString "b",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_u256_sub,.comb [.one,.one,.one,.one]) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "u256_sub") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "u256_sub") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "u256_sub")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 58 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original58 :: declarations.drop 59 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 59)).reverse).all
          (fun entry => !((ofString "u256_sub") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original58 :: declarations.drop 59) =
          (ofString "u256_sub",[(ofString "a",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "b",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_u256_sub,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 59) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original58_eq]
        simp only [Guest.guestFn_u256_sub,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "u256_sub") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "u256_sub") (functionsHOL (declarations.drop 59)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "u256_sub") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_u256Sub_lookup

theorem originalRuntimeCode_bn254Init_lookup :
    originalRuntimeCode.lookup (ofString "bn254_init") =
      some ([],sourceFunctionBody Guest.guestFn_bn254_init,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "bn254_init") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "bn254_init") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "bn254_init")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 671 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original671 :: declarations.drop 672 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 672)).reverse).all
          (fun entry => !((ofString "bn254_init") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original671 :: declarations.drop 672) =
          (ofString "bn254_init",[],sourceFunctionBody Guest.guestFn_bn254_init,ShapeHOL.one) ::
            functionsHOL (declarations.drop 672) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original671_eq]
        simp only [Guest.guestFn_bn254_init,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "bn254_init") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "bn254_init") (functionsHOL (declarations.drop 672)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "bn254_init") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_bn254Init_lookup

end InitECandidate.Runtime
