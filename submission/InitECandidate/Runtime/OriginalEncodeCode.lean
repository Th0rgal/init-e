import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_rlpBeLen_lookup :
    originalRuntimeCode.lookup (ofString "rlp_be_len") =
      some ([(ofString "v",.one)],sourceFunctionBody Guest.guestFn_rlp_be_len,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "rlp_be_len") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "rlp_be_len") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "rlp_be_len")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 119 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original119 :: declarations.drop 120 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 120)).reverse).all
          (fun entry => !((ofString "rlp_be_len") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original119 :: declarations.drop 120) =
          (ofString "rlp_be_len",[(ofString "v",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_rlp_be_len,ShapeHOL.one) ::
            functionsHOL (declarations.drop 120) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original119_eq]
        simp only [Guest.guestFn_rlp_be_len,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "rlp_be_len") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "rlp_be_len") (functionsHOL (declarations.drop 120)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "rlp_be_len") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_rlpBeLen_lookup

theorem originalRuntimeCode_rlpPutBe_lookup :
    originalRuntimeCode.lookup (ofString "rlp_put_be") =
      some ([(ofString "dst",.one),(ofString "v",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_rlp_put_be,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "rlp_put_be") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "rlp_put_be") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "rlp_put_be")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 120 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original120 :: declarations.drop 121 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 121)).reverse).all
          (fun entry => !((ofString "rlp_put_be") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original120 :: declarations.drop 121) =
          (ofString "rlp_put_be",[(ofString "dst",ShapeHOL.one),(ofString "v",ShapeHOL.one),(ofString "n",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_rlp_put_be,ShapeHOL.one) ::
            functionsHOL (declarations.drop 121) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original120_eq]
        simp only [Guest.guestFn_rlp_put_be,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "rlp_put_be") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "rlp_put_be") (functionsHOL (declarations.drop 121)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "rlp_put_be") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_rlpPutBe_lookup

theorem originalRuntimeCode_rlpWriteHeader_lookup :
    originalRuntimeCode.lookup (ofString "rlp_write_header") =
      some ([(ofString "dst",.one),(ofString "base",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_rlp_write_header,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "rlp_write_header") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "rlp_write_header") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "rlp_write_header")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 121 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original121 :: declarations.drop 122 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 122)).reverse).all
          (fun entry => !((ofString "rlp_write_header") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original121 :: declarations.drop 122) =
          (ofString "rlp_write_header",[(ofString "dst",ShapeHOL.one),(ofString "base",ShapeHOL.one),(ofString "n",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_rlp_write_header,ShapeHOL.one) ::
            functionsHOL (declarations.drop 122) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original121_eq]
        simp only [Guest.guestFn_rlp_write_header,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "rlp_write_header") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "rlp_write_header") (functionsHOL (declarations.drop 122)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "rlp_write_header") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_rlpWriteHeader_lookup

theorem originalRuntimeCode_rlpHeaderLen_lookup :
    originalRuntimeCode.lookup (ofString "rlp_header_len") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_rlp_header_len,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "rlp_header_len") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "rlp_header_len") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "rlp_header_len")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 122 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original122 :: declarations.drop 123 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 123)).reverse).all
          (fun entry => !((ofString "rlp_header_len") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original122 :: declarations.drop 123) =
          (ofString "rlp_header_len",[(ofString "n",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_rlp_header_len,ShapeHOL.one) ::
            functionsHOL (declarations.drop 123) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original122_eq]
        simp only [Guest.guestFn_rlp_header_len,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "rlp_header_len") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "rlp_header_len") (functionsHOL (declarations.drop 123)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "rlp_header_len") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_rlpHeaderLen_lookup

theorem originalRuntimeCode_rlpEncodeBytes_lookup :
    originalRuntimeCode.lookup (ofString "rlp_encode_bytes") =
      some ([(ofString "dst",.one),(ofString "src",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_rlp_encode_bytes,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "rlp_encode_bytes") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "rlp_encode_bytes") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "rlp_encode_bytes")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 123 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original123 :: declarations.drop 124 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 124)).reverse).all
          (fun entry => !((ofString "rlp_encode_bytes") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original123 :: declarations.drop 124) =
          (ofString "rlp_encode_bytes",[(ofString "dst",ShapeHOL.one),(ofString "src",ShapeHOL.one),(ofString "n",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_rlp_encode_bytes,ShapeHOL.one) ::
            functionsHOL (declarations.drop 124) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original123_eq]
        simp only [Guest.guestFn_rlp_encode_bytes,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "rlp_encode_bytes") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "rlp_encode_bytes") (functionsHOL (declarations.drop 124)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "rlp_encode_bytes") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_rlpEncodeBytes_lookup

theorem originalRuntimeCode_rlpEncodeWord_lookup :
    originalRuntimeCode.lookup (ofString "rlp_encode_word") =
      some ([(ofString "dst",.one),(ofString "w",.one)],sourceFunctionBody Guest.guestFn_rlp_encode_word,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "rlp_encode_word") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "rlp_encode_word") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "rlp_encode_word")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 124 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original124 :: declarations.drop 125 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 125)).reverse).all
          (fun entry => !((ofString "rlp_encode_word") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original124 :: declarations.drop 125) =
          (ofString "rlp_encode_word",[(ofString "dst",ShapeHOL.one),(ofString "w",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_rlp_encode_word,ShapeHOL.one) ::
            functionsHOL (declarations.drop 125) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original124_eq]
        simp only [Guest.guestFn_rlp_encode_word,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "rlp_encode_word") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "rlp_encode_word") (functionsHOL (declarations.drop 125)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "rlp_encode_word") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_rlpEncodeWord_lookup

theorem originalRuntimeCode_rlpEncodeListHeader_lookup :
    originalRuntimeCode.lookup (ofString "rlp_encode_list_header") =
      some ([(ofString "dst",.one),(ofString "payload_len",.one)],sourceFunctionBody Guest.guestFn_rlp_encode_list_header,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "rlp_encode_list_header") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "rlp_encode_list_header") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "rlp_encode_list_header")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 125 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original125 :: declarations.drop 126 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 126)).reverse).all
          (fun entry => !((ofString "rlp_encode_list_header") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original125 :: declarations.drop 126) =
          (ofString "rlp_encode_list_header",[(ofString "dst",ShapeHOL.one),(ofString "payload_len",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_rlp_encode_list_header,ShapeHOL.one) ::
            functionsHOL (declarations.drop 126) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original125_eq]
        simp only [Guest.guestFn_rlp_encode_list_header,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "rlp_encode_list_header") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "rlp_encode_list_header") (functionsHOL (declarations.drop 126)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "rlp_encode_list_header") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_rlpEncodeListHeader_lookup

theorem originalRuntimeCode_rlpListHeaderLen_lookup :
    originalRuntimeCode.lookup (ofString "rlp_list_header_len") =
      some ([(ofString "payload_len",.one)],sourceFunctionBody Guest.guestFn_rlp_list_header_len,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "rlp_list_header_len") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "rlp_list_header_len") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "rlp_list_header_len")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 127 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original127 :: declarations.drop 128 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 128)).reverse).all
          (fun entry => !((ofString "rlp_list_header_len") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original127 :: declarations.drop 128) =
          (ofString "rlp_list_header_len",[(ofString "payload_len",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_rlp_list_header_len,ShapeHOL.one) ::
            functionsHOL (declarations.drop 128) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original127_eq]
        simp only [Guest.guestFn_rlp_list_header_len,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "rlp_list_header_len") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "rlp_list_header_len") (functionsHOL (declarations.drop 128)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "rlp_list_header_len") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_rlpListHeaderLen_lookup

theorem originalRuntimeCode_rlpWordEncodedLen_lookup :
    originalRuntimeCode.lookup (ofString "rlp_word_encoded_len") =
      some ([(ofString "w",.one)],sourceFunctionBody Guest.guestFn_rlp_word_encoded_len,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "rlp_word_encoded_len") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "rlp_word_encoded_len") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "rlp_word_encoded_len")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 128 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original128 :: declarations.drop 129 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 129)).reverse).all
          (fun entry => !((ofString "rlp_word_encoded_len") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original128 :: declarations.drop 129) =
          (ofString "rlp_word_encoded_len",[(ofString "w",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_rlp_word_encoded_len,ShapeHOL.one) ::
            functionsHOL (declarations.drop 129) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original128_eq]
        simp only [Guest.guestFn_rlp_word_encoded_len,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "rlp_word_encoded_len") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "rlp_word_encoded_len") (functionsHOL (declarations.drop 129)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "rlp_word_encoded_len") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_rlpWordEncodedLen_lookup

theorem originalRuntimeCode_u256ToBeMin_lookup :
    originalRuntimeCode.lookup (ofString "u256_to_be_min") =
      some ([(ofString "a",.comb [.one,.one,.one,.one]),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_u256_to_be_min,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "u256_to_be_min") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "u256_to_be_min") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "u256_to_be_min")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 89 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original89 :: declarations.drop 90 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 90)).reverse).all
          (fun entry => !((ofString "u256_to_be_min") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original89 :: declarations.drop 90) =
          (ofString "u256_to_be_min",[(ofString "a",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "out",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_u256_to_be_min,ShapeHOL.one) ::
            functionsHOL (declarations.drop 90) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original89_eq]
        simp only [Guest.guestFn_u256_to_be_min,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "u256_to_be_min") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "u256_to_be_min") (functionsHOL (declarations.drop 90)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "u256_to_be_min") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_u256ToBeMin_lookup

theorem originalRuntimeCode_txPutU256_lookup :
    originalRuntimeCode.lookup (ofString "tx_put_u256") =
      some ([(ofString "dst",.one),(ofString "v",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_tx_put_u256,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "tx_put_u256") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "tx_put_u256") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "tx_put_u256")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 321 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original321 :: declarations.drop 322 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 322)).reverse).all
          (fun entry => !((ofString "tx_put_u256") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original321 :: declarations.drop 322) =
          (ofString "tx_put_u256",[(ofString "dst",ShapeHOL.one),(ofString "v",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_tx_put_u256,ShapeHOL.one) ::
            functionsHOL (declarations.drop 322) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original321_eq]
        simp only [Guest.guestFn_tx_put_u256,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "tx_put_u256") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "tx_put_u256") (functionsHOL (declarations.drop 322)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "tx_put_u256") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_txPutU256_lookup

theorem originalRuntimeCode_txPutTo_lookup :
    originalRuntimeCode.lookup (ofString "tx_put_to") =
      some ([(ofString "dst",.one),(ofString "to",.one)],sourceFunctionBody Guest.guestFn_tx_put_to,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "tx_put_to") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "tx_put_to") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "tx_put_to")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 323 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original323 :: declarations.drop 324 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 324)).reverse).all
          (fun entry => !((ofString "tx_put_to") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original323 :: declarations.drop 324) =
          (ofString "tx_put_to",[(ofString "dst",ShapeHOL.one),(ofString "to",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_tx_put_to,ShapeHOL.one) ::
            functionsHOL (declarations.drop 324) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original323_eq]
        simp only [Guest.guestFn_tx_put_to,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "tx_put_to") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "tx_put_to") (functionsHOL (declarations.drop 324)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "tx_put_to") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_txPutTo_lookup

theorem originalRuntimeCode_accessListPayloadLen_lookup :
    originalRuntimeCode.lookup (ofString "access_list_payload_len") =
      some ([(ofString "recs",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_access_list_payload_len,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "access_list_payload_len") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "access_list_payload_len") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "access_list_payload_len")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 324 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original324 :: declarations.drop 325 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 325)).reverse).all
          (fun entry => !((ofString "access_list_payload_len") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original324 :: declarations.drop 325) =
          (ofString "access_list_payload_len",[(ofString "recs",ShapeHOL.one),(ofString "n",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_access_list_payload_len,ShapeHOL.one) ::
            functionsHOL (declarations.drop 325) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original324_eq]
        simp only [Guest.guestFn_access_list_payload_len,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "access_list_payload_len") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "access_list_payload_len") (functionsHOL (declarations.drop 325)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "access_list_payload_len") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_accessListPayloadLen_lookup

theorem originalRuntimeCode_txPutAccessList_lookup :
    originalRuntimeCode.lookup (ofString "tx_put_access_list") =
      some ([(ofString "dst",.one),(ofString "recs",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_tx_put_access_list,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "tx_put_access_list") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "tx_put_access_list") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "tx_put_access_list")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 325 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original325 :: declarations.drop 326 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 326)).reverse).all
          (fun entry => !((ofString "tx_put_access_list") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original325 :: declarations.drop 326) =
          (ofString "tx_put_access_list",[(ofString "dst",ShapeHOL.one),(ofString "recs",ShapeHOL.one),(ofString "n",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_tx_put_access_list,ShapeHOL.one) ::
            functionsHOL (declarations.drop 326) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original325_eq]
        simp only [Guest.guestFn_tx_put_access_list,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "tx_put_access_list") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "tx_put_access_list") (functionsHOL (declarations.drop 326)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "tx_put_access_list") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_txPutAccessList_lookup

theorem originalRuntimeCode_txPutBlobHashes_lookup :
    originalRuntimeCode.lookup (ofString "tx_put_blob_hashes") =
      some ([(ofString "dst",.one),(ofString "buf",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_tx_put_blob_hashes,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "tx_put_blob_hashes") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "tx_put_blob_hashes") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "tx_put_blob_hashes")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 326 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original326 :: declarations.drop 327 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 327)).reverse).all
          (fun entry => !((ofString "tx_put_blob_hashes") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original326 :: declarations.drop 327) =
          (ofString "tx_put_blob_hashes",[(ofString "dst",ShapeHOL.one),(ofString "buf",ShapeHOL.one),(ofString "n",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_tx_put_blob_hashes,ShapeHOL.one) ::
            functionsHOL (declarations.drop 327) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original326_eq]
        simp only [Guest.guestFn_tx_put_blob_hashes,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "tx_put_blob_hashes") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "tx_put_blob_hashes") (functionsHOL (declarations.drop 327)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "tx_put_blob_hashes") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_txPutBlobHashes_lookup

theorem originalRuntimeCode_authPayloadLen_lookup :
    originalRuntimeCode.lookup (ofString "auth_payload_len") =
      some ([(ofString "a",.one)],sourceFunctionBody Guest.guestFn_auth_payload_len,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "auth_payload_len") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "auth_payload_len") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "auth_payload_len")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 327 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original327 :: declarations.drop 328 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 328)).reverse).all
          (fun entry => !((ofString "auth_payload_len") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original327 :: declarations.drop 328) =
          (ofString "auth_payload_len",[(ofString "a",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_auth_payload_len,ShapeHOL.one) ::
            functionsHOL (declarations.drop 328) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original327_eq]
        simp only [Guest.guestFn_auth_payload_len,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "auth_payload_len") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "auth_payload_len") (functionsHOL (declarations.drop 328)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "auth_payload_len") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_authPayloadLen_lookup

theorem originalRuntimeCode_authListPayloadLen_lookup :
    originalRuntimeCode.lookup (ofString "auth_list_payload_len") =
      some ([(ofString "recs",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_auth_list_payload_len,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "auth_list_payload_len") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "auth_list_payload_len") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "auth_list_payload_len")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 328 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original328 :: declarations.drop 329 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 329)).reverse).all
          (fun entry => !((ofString "auth_list_payload_len") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original328 :: declarations.drop 329) =
          (ofString "auth_list_payload_len",[(ofString "recs",ShapeHOL.one),(ofString "n",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_auth_list_payload_len,ShapeHOL.one) ::
            functionsHOL (declarations.drop 329) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original328_eq]
        simp only [Guest.guestFn_auth_list_payload_len,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "auth_list_payload_len") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "auth_list_payload_len") (functionsHOL (declarations.drop 329)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "auth_list_payload_len") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_authListPayloadLen_lookup

theorem originalRuntimeCode_txPutAuthorizations_lookup :
    originalRuntimeCode.lookup (ofString "tx_put_authorizations") =
      some ([(ofString "dst",.one),(ofString "recs",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_tx_put_authorizations,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "tx_put_authorizations") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "tx_put_authorizations") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "tx_put_authorizations")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 329 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original329 :: declarations.drop 330 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 330)).reverse).all
          (fun entry => !((ofString "tx_put_authorizations") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original329 :: declarations.drop 330) =
          (ofString "tx_put_authorizations",[(ofString "dst",ShapeHOL.one),(ofString "recs",ShapeHOL.one),(ofString "n",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_tx_put_authorizations,ShapeHOL.one) ::
            functionsHOL (declarations.drop 330) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original329_eq]
        simp only [Guest.guestFn_tx_put_authorizations,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "tx_put_authorizations") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "tx_put_authorizations") (functionsHOL (declarations.drop 330)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "tx_put_authorizations") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_txPutAuthorizations_lookup

theorem originalRuntimeCode_txEncodeBound_lookup :
    originalRuntimeCode.lookup (ofString "tx_encode_bound") =
      some ([(ofString "tx",.one)],sourceFunctionBody Guest.guestFn_tx_encode_bound,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "tx_encode_bound") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "tx_encode_bound") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "tx_encode_bound")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 330 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original330 :: declarations.drop 331 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 331)).reverse).all
          (fun entry => !((ofString "tx_encode_bound") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original330 :: declarations.drop 331) =
          (ofString "tx_encode_bound",[(ofString "tx",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_tx_encode_bound,ShapeHOL.one) ::
            functionsHOL (declarations.drop 331) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original330_eq]
        simp only [Guest.guestFn_tx_encode_bound,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "tx_encode_bound") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "tx_encode_bound") (functionsHOL (declarations.drop 331)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "tx_encode_bound") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_txEncodeBound_lookup

theorem originalRuntimeCode_txEncodeGeneric_lookup :
    originalRuntimeCode.lookup (ofString "tx_encode_generic") =
      some ([(ofString "tx",.one),(ofString "mode",.one),(ofString "chain_id",.one)],sourceFunctionBody Guest.guestFn_tx_encode_generic,(.comb [.one,.one])) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "tx_encode_generic") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "tx_encode_generic") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "tx_encode_generic")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 331 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original331 :: declarations.drop 332 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 332)).reverse).all
          (fun entry => !((ofString "tx_encode_generic") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original331 :: declarations.drop 332) =
          (ofString "tx_encode_generic",[(ofString "tx",ShapeHOL.one),(ofString "mode",ShapeHOL.one),(ofString "chain_id",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_tx_encode_generic,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 332) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original331_eq]
        simp only [Guest.guestFn_tx_encode_generic,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "tx_encode_generic") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "tx_encode_generic") (functionsHOL (declarations.drop 332)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "tx_encode_generic") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_txEncodeGeneric_lookup

end InitECandidate.Runtime
