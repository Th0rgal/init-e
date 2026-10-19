import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_hdrUintField_lookup :
    originalRuntimeCode.lookup (ofString "hdr_uint_field") =
      some ([(ofString "arr",.one),(ofString "i",.one),(ofString "maxb",.one)],sourceFunctionBody Guest.guestFn_hdr_uint_field,.comb [.one,.one]) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "hdr_uint_field") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "hdr_uint_field") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "hdr_uint_field")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 225 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original225 :: declarations.drop 226 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 226)).reverse).all
          (fun entry => !((ofString "hdr_uint_field") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original225 :: declarations.drop 226) =
          (ofString "hdr_uint_field",[(ofString "arr",ShapeHOL.one),(ofString "i",ShapeHOL.one),(ofString "maxb",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_hdr_uint_field,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 226) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original225_eq]
        simp only [Guest.guestFn_hdr_uint_field,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "hdr_uint_field") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "hdr_uint_field") (functionsHOL (declarations.drop 226)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "hdr_uint_field") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_hdrUintField_lookup


theorem originalRuntimeCode_hdrBytesField_lookup :
    originalRuntimeCode.lookup (ofString "hdr_bytes_field") =
      some ([(ofString "arr",.one),(ofString "i",.one),(ofString "width",.one)],sourceFunctionBody Guest.guestFn_hdr_bytes_field,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "hdr_bytes_field") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "hdr_bytes_field") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "hdr_bytes_field")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 228 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original228 :: declarations.drop 229 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 229)).reverse).all
          (fun entry => !((ofString "hdr_bytes_field") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original228 :: declarations.drop 229) =
          (ofString "hdr_bytes_field",[(ofString "arr",ShapeHOL.one),(ofString "i",ShapeHOL.one),(ofString "width",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_hdr_bytes_field,ShapeHOL.one) ::
            functionsHOL (declarations.drop 229) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original228_eq]
        simp only [Guest.guestFn_hdr_bytes_field,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "hdr_bytes_field") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "hdr_bytes_field") (functionsHOL (declarations.drop 229)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "hdr_bytes_field") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_hdrBytesField_lookup


theorem originalRuntimeCode_hdrRawField_lookup :
    originalRuntimeCode.lookup (ofString "hdr_raw_field") =
      some ([(ofString "arr",.one),(ofString "i",.one)],sourceFunctionBody Guest.guestFn_hdr_raw_field,.comb [.one,.one]) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "hdr_raw_field") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "hdr_raw_field") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "hdr_raw_field")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 229 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original229 :: declarations.drop 230 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 230)).reverse).all
          (fun entry => !((ofString "hdr_raw_field") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original229 :: declarations.drop 230) =
          (ofString "hdr_raw_field",[(ofString "arr",ShapeHOL.one),(ofString "i",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_hdr_raw_field,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 230) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original229_eq]
        simp only [Guest.guestFn_hdr_raw_field,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "hdr_raw_field") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "hdr_raw_field") (functionsHOL (declarations.drop 230)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "hdr_raw_field") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_hdrRawField_lookup

end InitECandidate.Runtime
