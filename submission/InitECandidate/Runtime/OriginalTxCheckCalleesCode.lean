import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_u256FitsWord_lookup :
    originalRuntimeCode.lookup (ofString "u256_fits_word") =
      some ([(ofString "a",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_u256_fits_word,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "u256_fits_word") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "u256_fits_word") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "u256_fits_word")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 42 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original42 :: declarations.drop 43 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 43)).reverse).all
          (fun entry => !((ofString "u256_fits_word") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original42 :: declarations.drop 43) =
          (ofString "u256_fits_word",[(ofString "a",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_u256_fits_word,ShapeHOL.one) ::
            functionsHOL (declarations.drop 43) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original42_eq]
        simp only [Guest.guestFn_u256_fits_word,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "u256_fits_word") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "u256_fits_word") (functionsHOL (declarations.drop 43)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "u256_fits_word") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_u256FitsWord_lookup

theorem originalRuntimeCode_u256Lt_lookup :
    originalRuntimeCode.lookup (ofString "u256_lt") =
      some ([(ofString "a",.comb [.one,.one,.one,.one]),(ofString "b",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_u256_lt,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "u256_lt") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "u256_lt") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "u256_lt")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 47 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original47 :: declarations.drop 48 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 48)).reverse).all
          (fun entry => !((ofString "u256_lt") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original47 :: declarations.drop 48) =
          (ofString "u256_lt",[(ofString "a",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "b",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_u256_lt,ShapeHOL.one) ::
            functionsHOL (declarations.drop 48) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original47_eq]
        simp only [Guest.guestFn_u256_lt,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "u256_lt") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "u256_lt") (functionsHOL (declarations.drop 48)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "u256_lt") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_u256Lt_lookup

theorem originalRuntimeCode_u256AddCarry_lookup :
    originalRuntimeCode.lookup (ofString "u256_add_carry") =
      some ([(ofString "a",.comb [.one,.one,.one,.one]),(ofString "b",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_u256_add_carry,(.comb [.one,.one,.one,.one,.one])) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "u256_add_carry") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "u256_add_carry") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "u256_add_carry")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 56 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original56 :: declarations.drop 57 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 57)).reverse).all
          (fun entry => !((ofString "u256_add_carry") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original56 :: declarations.drop 57) =
          (ofString "u256_add_carry",[(ofString "a",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "b",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_u256_add_carry,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 57) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original56_eq]
        simp only [Guest.guestFn_u256_add_carry,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "u256_add_carry") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "u256_add_carry") (functionsHOL (declarations.drop 57)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "u256_add_carry") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_u256AddCarry_lookup

theorem originalRuntimeCode_u256Add_lookup :
    originalRuntimeCode.lookup (ofString "u256_add") =
      some ([(ofString "a",.comb [.one,.one,.one,.one]),(ofString "b",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_u256_add,(.comb [.one,.one,.one,.one])) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "u256_add") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "u256_add") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "u256_add")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 57 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original57 :: declarations.drop 58 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 58)).reverse).all
          (fun entry => !((ofString "u256_add") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original57 :: declarations.drop 58) =
          (ofString "u256_add",[(ofString "a",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "b",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_u256_add,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 58) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original57_eq]
        simp only [Guest.guestFn_u256_add,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "u256_add") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "u256_add") (functionsHOL (declarations.drop 58)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "u256_add") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_u256Add_lookup

theorem originalRuntimeCode_isValidDelegation_lookup :
    originalRuntimeCode.lookup (ofString "is_valid_delegation") =
      some ([(ofString "code",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_is_valid_delegation,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "is_valid_delegation") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "is_valid_delegation") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "is_valid_delegation")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 449 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original449 :: declarations.drop 450 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 450)).reverse).all
          (fun entry => !((ofString "is_valid_delegation") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original449 :: declarations.drop 450) =
          (ofString "is_valid_delegation",[(ofString "code",ShapeHOL.one),(ofString "n",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_is_valid_delegation,ShapeHOL.one) ::
            functionsHOL (declarations.drop 450) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original449_eq]
        simp only [Guest.guestFn_is_valid_delegation,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "is_valid_delegation") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "is_valid_delegation") (functionsHOL (declarations.drop 450)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "is_valid_delegation") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_isValidDelegation_lookup

end InitECandidate.Runtime
