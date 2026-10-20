import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_div64by32_lookup :
    originalRuntimeCode.lookup (ofString "div64by32") =
      some ([(ofString "hi",.one),(ofString "lo",.one),(ofString "d",.one)],sourceFunctionBody Guest.guestFn_div64by32,(.comb [.one,.one])) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "div64by32") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "div64by32") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "div64by32")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 64 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original64 :: declarations.drop 65 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 65)).reverse).all
          (fun entry => !((ofString "div64by32") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original64 :: declarations.drop 65) =
          (ofString "div64by32",[(ofString "hi",ShapeHOL.one),(ofString "lo",ShapeHOL.one),(ofString "d",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_div64by32,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 65) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original64_eq]
        simp only [Guest.guestFn_div64by32,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "div64by32") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "div64by32") (functionsHOL (declarations.drop 65)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "div64by32") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_div64by32_lookup

theorem originalRuntimeCode_digitsLen_lookup :
    originalRuntimeCode.lookup (ofString "digits_len") =
      some ([(ofString "p",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_digits_len,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "digits_len") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "digits_len") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "digits_len")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 67 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original67 :: declarations.drop 68 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 68)).reverse).all
          (fun entry => !((ofString "digits_len") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original67 :: declarations.drop 68) =
          (ofString "digits_len",[(ofString "p",ShapeHOL.one),(ofString "n",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_digits_len,ShapeHOL.one) ::
            functionsHOL (declarations.drop 68) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original67_eq]
        simp only [Guest.guestFn_digits_len,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "digits_len") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "digits_len") (functionsHOL (declarations.drop 68)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "digits_len") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_digitsLen_lookup

theorem originalRuntimeCode_divmnu_lookup :
    originalRuntimeCode.lookup (ofString "divmnu") =
      some ([(ofString "q",.one),(ofString "r",.one),(ofString "u",.one),(ofString "m",.one),(ofString "v",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_divmnu,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "divmnu") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "divmnu") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "divmnu")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 68 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original68 :: declarations.drop 69 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 69)).reverse).all
          (fun entry => !((ofString "divmnu") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original68 :: declarations.drop 69) =
          (ofString "divmnu",[(ofString "q",ShapeHOL.one),(ofString "r",ShapeHOL.one),(ofString "u",ShapeHOL.one),(ofString "m",ShapeHOL.one),(ofString "v",ShapeHOL.one),(ofString "n",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_divmnu,ShapeHOL.one) ::
            functionsHOL (declarations.drop 69) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original68_eq]
        simp only [Guest.guestFn_divmnu,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "divmnu") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "divmnu") (functionsHOL (declarations.drop 69)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "divmnu") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_divmnu_lookup

theorem originalRuntimeCode_digitsDivmod_lookup :
    originalRuntimeCode.lookup (ofString "digits_divmod") =
      some ([(ofString "u",.one),(ofString "m",.one),(ofString "d",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_digits_divmod,(.comb [.one,.one,.one,.one])) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "digits_divmod") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "digits_divmod") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "digits_divmod")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 69 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original69 :: declarations.drop 70 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 70)).reverse).all
          (fun entry => !((ofString "digits_divmod") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original69 :: declarations.drop 70) =
          (ofString "digits_divmod",[(ofString "u",ShapeHOL.one),(ofString "m",ShapeHOL.one),(ofString "d",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_digits_divmod,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 70) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original69_eq]
        simp only [Guest.guestFn_digits_divmod,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "digits_divmod") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "digits_divmod") (functionsHOL (declarations.drop 70)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "digits_divmod") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_digitsDivmod_lookup

theorem originalRuntimeCode_u256Divmod_lookup :
    originalRuntimeCode.lookup (ofString "u256_divmod") =
      some ([(ofString "a",.comb [.one,.one,.one,.one]),(ofString "b",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_u256_divmod,(.comb [.one,.one,.one,.one,.one,.one,.one,.one])) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "u256_divmod") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "u256_divmod") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "u256_divmod")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 70 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original70 :: declarations.drop 71 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 71)).reverse).all
          (fun entry => !((ofString "u256_divmod") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original70 :: declarations.drop 71) =
          (ofString "u256_divmod",[(ofString "a",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "b",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_u256_divmod,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 71) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original70_eq]
        simp only [Guest.guestFn_u256_divmod,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "u256_divmod") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "u256_divmod") (functionsHOL (declarations.drop 71)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "u256_divmod") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_u256Divmod_lookup

theorem originalRuntimeCode_u256Div_lookup :
    originalRuntimeCode.lookup (ofString "u256_div") =
      some ([(ofString "a",.comb [.one,.one,.one,.one]),(ofString "b",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_u256_div,(.comb [.one,.one,.one,.one])) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "u256_div") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "u256_div") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "u256_div")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 71 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original71 :: declarations.drop 72 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 72)).reverse).all
          (fun entry => !((ofString "u256_div") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original71 :: declarations.drop 72) =
          (ofString "u256_div",[(ofString "a",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "b",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_u256_div,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 72) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original71_eq]
        simp only [Guest.guestFn_u256_div,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "u256_div") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "u256_div") (functionsHOL (declarations.drop 72)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "u256_div") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_u256Div_lookup

theorem originalRuntimeCode_taylorExponential_lookup :
    originalRuntimeCode.lookup (ofString "taylor_exponential") =
      some ([(ofString "factor",.one),(ofString "numerator",.one),(ofString "denominator",.one)],sourceFunctionBody Guest.guestFn_taylor_exponential,(.comb [.one,.one,.one,.one])) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "taylor_exponential") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "taylor_exponential") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "taylor_exponential")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 235 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original235 :: declarations.drop 236 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 236)).reverse).all
          (fun entry => !((ofString "taylor_exponential") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original235 :: declarations.drop 236) =
          (ofString "taylor_exponential",[(ofString "factor",ShapeHOL.one),(ofString "numerator",ShapeHOL.one),(ofString "denominator",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_taylor_exponential,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 236) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original235_eq]
        simp only [Guest.guestFn_taylor_exponential,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "taylor_exponential") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "taylor_exponential") (functionsHOL (declarations.drop 236)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "taylor_exponential") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_taylorExponential_lookup

end InitECandidate.Runtime
