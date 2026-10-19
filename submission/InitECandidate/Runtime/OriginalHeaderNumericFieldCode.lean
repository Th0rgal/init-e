import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_hdrWordField_lookup :
    originalRuntimeCode.lookup (ofString "hdr_word_field") =
      some ([(ofString "arr",.one),(ofString "i",.one)],sourceFunctionBody Guest.guestFn_hdr_word_field,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "hdr_word_field") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "hdr_word_field") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "hdr_word_field")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 226 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original226 :: declarations.drop 227 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 227)).reverse).all
          (fun entry => !((ofString "hdr_word_field") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original226 :: declarations.drop 227) =
          (ofString "hdr_word_field",[(ofString "arr",ShapeHOL.one),(ofString "i",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_hdr_word_field,ShapeHOL.one) ::
            functionsHOL (declarations.drop 227) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original226_eq]
        simp only [Guest.guestFn_hdr_word_field,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "hdr_word_field") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "hdr_word_field") (functionsHOL (declarations.drop 227)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "hdr_word_field") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_hdrWordField_lookup


theorem originalRuntimeCode_hdrU256Field_lookup :
    originalRuntimeCode.lookup (ofString "hdr_u256_field") =
      some ([(ofString "arr",.one),(ofString "i",.one),(ofString "maxb",.one)],sourceFunctionBody Guest.guestFn_hdr_u256_field,.comb [.one,.one,.one,.one]) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "hdr_u256_field") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "hdr_u256_field") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "hdr_u256_field")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 227 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original227 :: declarations.drop 228 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 228)).reverse).all
          (fun entry => !((ofString "hdr_u256_field") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original227 :: declarations.drop 228) =
          (ofString "hdr_u256_field",[(ofString "arr",ShapeHOL.one),(ofString "i",ShapeHOL.one),(ofString "maxb",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_hdr_u256_field,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 228) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original227_eq]
        simp only [Guest.guestFn_hdr_u256_field,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "hdr_u256_field") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "hdr_u256_field") (functionsHOL (declarations.drop 228)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "hdr_u256_field") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_hdrU256Field_lookup

end InitECandidate.Runtime
