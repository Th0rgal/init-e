import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_htrDeposit_lookup :
    originalRuntimeCode.lookup (ofString "htr_deposit") =
      some ([(ofString "e",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_htr_deposit,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "htr_deposit") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "htr_deposit") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "htr_deposit")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 214 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original214 :: declarations.drop 215 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 215)).reverse).all
          (fun entry => !((ofString "htr_deposit") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original214 :: declarations.drop 215) =
          (ofString "htr_deposit",[(ofString "e",ShapeHOL.one),(ofString "out",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_htr_deposit,ShapeHOL.one) ::
            functionsHOL (declarations.drop 215) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original214_eq]
        simp only [Guest.guestFn_htr_deposit,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "htr_deposit") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "htr_deposit") (functionsHOL (declarations.drop 215)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "htr_deposit") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_htrDeposit_lookup

theorem originalRuntimeCode_htrWdreq_lookup :
    originalRuntimeCode.lookup (ofString "htr_wdreq") =
      some ([(ofString "e",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_htr_wdreq,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "htr_wdreq") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "htr_wdreq") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "htr_wdreq")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 215 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original215 :: declarations.drop 216 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 216)).reverse).all
          (fun entry => !((ofString "htr_wdreq") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original215 :: declarations.drop 216) =
          (ofString "htr_wdreq",[(ofString "e",ShapeHOL.one),(ofString "out",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_htr_wdreq,ShapeHOL.one) ::
            functionsHOL (declarations.drop 216) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original215_eq]
        simp only [Guest.guestFn_htr_wdreq,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "htr_wdreq") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "htr_wdreq") (functionsHOL (declarations.drop 216)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "htr_wdreq") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_htrWdreq_lookup

theorem originalRuntimeCode_htrCons_lookup :
    originalRuntimeCode.lookup (ofString "htr_cons") =
      some ([(ofString "e",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_htr_cons,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "htr_cons") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "htr_cons") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "htr_cons")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 216 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original216 :: declarations.drop 217 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 217)).reverse).all
          (fun entry => !((ofString "htr_cons") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original216 :: declarations.drop 217) =
          (ofString "htr_cons",[(ofString "e",ShapeHOL.one),(ofString "out",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_htr_cons,ShapeHOL.one) ::
            functionsHOL (declarations.drop 217) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original216_eq]
        simp only [Guest.guestFn_htr_cons,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "htr_cons") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "htr_cons") (functionsHOL (declarations.drop 217)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "htr_cons") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_htrCons_lookup

theorem originalRuntimeCode_htrBdep_lookup :
    originalRuntimeCode.lookup (ofString "htr_bdep") =
      some ([(ofString "e",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_htr_bdep,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "htr_bdep") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "htr_bdep") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "htr_bdep")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 217 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original217 :: declarations.drop 218 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 218)).reverse).all
          (fun entry => !((ofString "htr_bdep") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original217 :: declarations.drop 218) =
          (ofString "htr_bdep",[(ofString "e",ShapeHOL.one),(ofString "out",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_htr_bdep,ShapeHOL.one) ::
            functionsHOL (declarations.drop 218) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original217_eq]
        simp only [Guest.guestFn_htr_bdep,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "htr_bdep") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "htr_bdep") (functionsHOL (declarations.drop 218)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "htr_bdep") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_htrBdep_lookup

theorem originalRuntimeCode_htrBexit_lookup :
    originalRuntimeCode.lookup (ofString "htr_bexit") =
      some ([(ofString "e",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_htr_bexit,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "htr_bexit") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "htr_bexit") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "htr_bexit")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 218 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original218 :: declarations.drop 219 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 219)).reverse).all
          (fun entry => !((ofString "htr_bexit") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original218 :: declarations.drop 219) =
          (ofString "htr_bexit",[(ofString "e",ShapeHOL.one),(ofString "out",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_htr_bexit,ShapeHOL.one) ::
            functionsHOL (declarations.drop 219) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original218_eq]
        simp only [Guest.guestFn_htr_bexit,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "htr_bexit") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "htr_bexit") (functionsHOL (declarations.drop 219)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "htr_bexit") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_htrBexit_lookup

end InitECandidate.Runtime
