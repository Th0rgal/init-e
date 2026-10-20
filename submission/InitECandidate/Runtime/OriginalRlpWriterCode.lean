import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.OriginalMemcpyCode
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendStages.Declarations

/-- The installed runtime code resolves a declaration that appears at a known position of the
`originals` list.  This is the shared proof skeleton of every `originalRuntimeCode_*_lookup` lemma:
the finite function is a reverse `FUPDATE_LIST`, so the last binding wins, and the binding at the
split point is the one we want. -/
theorem originalRuntimeCode_lookup_split (name : MlS)
    (before : List (DeclHOL 64)) (entry : DeclHOL 64) (after : List (DeclHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (whole : originals = before ++ entry :: after)
    (head : functionsHOL (entry :: after) = (name,parameters,body,returnShape) :: functionsHOL after)
    (absent : ((functionsHOL after).reverse).all (fun e => !(name == e.1)) = true) :
    originalRuntimeCode.lookup name = some (parameters,body,returnShape) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup name (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) name = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse name
    _ = _ := by
      rw [sourceDeclarations_eq,whole]
      change List.lookup name (functionsHOL (before ++ entry :: after)).reverse = _
      rw [functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup name (functionsHOL after).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup name (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_lookup_split

theorem originalRuntimeCode_rlp_be_len_lookup :
    originalRuntimeCode.lookup (ofString "rlp_be_len") =
      some ([(ofString "v",.one)],sourceFunctionBody Guest.guestFn_rlp_be_len,.one) := by
  refine originalRuntimeCode_lookup_split (ofString "rlp_be_len")
    (originals.take 119) original119 (originals.drop 120)
    [(ofString "v",.one)] (sourceFunctionBody Guest.guestFn_rlp_be_len) .one ?_ ?_ ?_
  · kernel_rfl
  · rw [original119_eq]
    simp only [Guest.guestFn_rlp_be_len,declToHOL,functionsHOL,funDeclToHOL,
      List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
  · decide_cbv

#print axioms originalRuntimeCode_rlp_be_len_lookup

theorem originalRuntimeCode_rlp_put_be_lookup :
    originalRuntimeCode.lookup (ofString "rlp_put_be") =
      some ([(ofString "dst",.one),(ofString "v",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_rlp_put_be,.one) := by
  refine originalRuntimeCode_lookup_split (ofString "rlp_put_be")
    (originals.take 120) original120 (originals.drop 121)
    [(ofString "dst",.one),(ofString "v",.one),(ofString "n",.one)] (sourceFunctionBody Guest.guestFn_rlp_put_be) .one ?_ ?_ ?_
  · kernel_rfl
  · rw [original120_eq]
    simp only [Guest.guestFn_rlp_put_be,declToHOL,functionsHOL,funDeclToHOL,
      List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
  · decide_cbv

#print axioms originalRuntimeCode_rlp_put_be_lookup

theorem originalRuntimeCode_rlp_write_header_lookup :
    originalRuntimeCode.lookup (ofString "rlp_write_header") =
      some ([(ofString "dst",.one),(ofString "base",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_rlp_write_header,.one) := by
  refine originalRuntimeCode_lookup_split (ofString "rlp_write_header")
    (originals.take 121) original121 (originals.drop 122)
    [(ofString "dst",.one),(ofString "base",.one),(ofString "n",.one)] (sourceFunctionBody Guest.guestFn_rlp_write_header) .one ?_ ?_ ?_
  · kernel_rfl
  · rw [original121_eq]
    simp only [Guest.guestFn_rlp_write_header,declToHOL,functionsHOL,funDeclToHOL,
      List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
  · decide_cbv

#print axioms originalRuntimeCode_rlp_write_header_lookup

theorem originalRuntimeCode_rlp_header_len_lookup :
    originalRuntimeCode.lookup (ofString "rlp_header_len") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_rlp_header_len,.one) := by
  refine originalRuntimeCode_lookup_split (ofString "rlp_header_len")
    (originals.take 122) original122 (originals.drop 123)
    [(ofString "n",.one)] (sourceFunctionBody Guest.guestFn_rlp_header_len) .one ?_ ?_ ?_
  · kernel_rfl
  · rw [original122_eq]
    simp only [Guest.guestFn_rlp_header_len,declToHOL,functionsHOL,funDeclToHOL,
      List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
  · decide_cbv

#print axioms originalRuntimeCode_rlp_header_len_lookup

theorem originalRuntimeCode_rlp_encode_bytes_lookup :
    originalRuntimeCode.lookup (ofString "rlp_encode_bytes") =
      some ([(ofString "dst",.one),(ofString "src",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_rlp_encode_bytes,.one) := by
  refine originalRuntimeCode_lookup_split (ofString "rlp_encode_bytes")
    (originals.take 123) original123 (originals.drop 124)
    [(ofString "dst",.one),(ofString "src",.one),(ofString "n",.one)] (sourceFunctionBody Guest.guestFn_rlp_encode_bytes) .one ?_ ?_ ?_
  · kernel_rfl
  · rw [original123_eq]
    simp only [Guest.guestFn_rlp_encode_bytes,declToHOL,functionsHOL,funDeclToHOL,
      List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
  · decide_cbv

#print axioms originalRuntimeCode_rlp_encode_bytes_lookup

theorem originalRuntimeCode_rlp_encode_word_lookup :
    originalRuntimeCode.lookup (ofString "rlp_encode_word") =
      some ([(ofString "dst",.one),(ofString "w",.one)],sourceFunctionBody Guest.guestFn_rlp_encode_word,.one) := by
  refine originalRuntimeCode_lookup_split (ofString "rlp_encode_word")
    (originals.take 124) original124 (originals.drop 125)
    [(ofString "dst",.one),(ofString "w",.one)] (sourceFunctionBody Guest.guestFn_rlp_encode_word) .one ?_ ?_ ?_
  · kernel_rfl
  · rw [original124_eq]
    simp only [Guest.guestFn_rlp_encode_word,declToHOL,functionsHOL,funDeclToHOL,
      List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
  · decide_cbv

#print axioms originalRuntimeCode_rlp_encode_word_lookup

theorem originalRuntimeCode_rlp_list_header_len_lookup :
    originalRuntimeCode.lookup (ofString "rlp_list_header_len") =
      some ([(ofString "payload_len",.one)],sourceFunctionBody Guest.guestFn_rlp_list_header_len,.one) := by
  refine originalRuntimeCode_lookup_split (ofString "rlp_list_header_len")
    (originals.take 127) original127 (originals.drop 128)
    [(ofString "payload_len",.one)] (sourceFunctionBody Guest.guestFn_rlp_list_header_len) .one ?_ ?_ ?_
  · kernel_rfl
  · rw [original127_eq]
    simp only [Guest.guestFn_rlp_list_header_len,declToHOL,functionsHOL,funDeclToHOL,
      List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
  · decide_cbv

#print axioms originalRuntimeCode_rlp_list_header_len_lookup

theorem originalRuntimeCode_rlp_finish_list_lookup :
    originalRuntimeCode.lookup (ofString "rlp_finish_list") =
      some ([(ofString "dst",.one),(ofString "payload_end",.one)],sourceFunctionBody Guest.guestFn_rlp_finish_list,.one) := by
  refine originalRuntimeCode_lookup_split (ofString "rlp_finish_list")
    (originals.take 872) original872 (originals.drop 873)
    [(ofString "dst",.one),(ofString "payload_end",.one)] (sourceFunctionBody Guest.guestFn_rlp_finish_list) .one ?_ ?_ ?_
  · kernel_rfl
  · rw [original872_eq]
    simp only [Guest.guestFn_rlp_finish_list,declToHOL,functionsHOL,funDeclToHOL,
      List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
  · decide_cbv

#print axioms originalRuntimeCode_rlp_finish_list_lookup

end InitECandidate.Runtime
