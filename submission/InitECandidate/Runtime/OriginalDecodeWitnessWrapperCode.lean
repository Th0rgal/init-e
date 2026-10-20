import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_decodeWitnessBody_lookup :
    originalRuntimeCode.lookup (ofString "_decode_witness_node_body") =
      some ([(ofString "db",.one),(ofString "p",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn__decode_witness_node_body,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "_decode_witness_node_body") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "_decode_witness_node_body") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "_decode_witness_node_body")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 265 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original265 :: declarations.drop 266 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 266)).reverse).all
          (fun entry => !((ofString "_decode_witness_node_body") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original265 :: declarations.drop 266) =
          (ofString "_decode_witness_node_body",[(ofString "db",ShapeHOL.one),(ofString "p",ShapeHOL.one),(ofString "n",ShapeHOL.one)],sourceFunctionBody Guest.guestFn__decode_witness_node_body,ShapeHOL.one) ::
            functionsHOL (declarations.drop 266) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original265_eq]
        simp only [Guest.guestFn__decode_witness_node_body,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "_decode_witness_node_body") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "_decode_witness_node_body") (functionsHOL (declarations.drop 266)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "_decode_witness_node_body") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_decodeWitnessBody_lookup

theorem originalRuntimeCode_decodeWitnessMpt_lookup :
    originalRuntimeCode.lookup (ofString "_decode_witness_node_mpt") =
      some ([(ofString "db",.one),(ofString "p",.one),(ofString "n",.one),(ofString "mark",.one)],sourceFunctionBody Guest.guestFn__decode_witness_node_mpt,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "_decode_witness_node_mpt") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "_decode_witness_node_mpt") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "_decode_witness_node_mpt")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 266 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original266 :: declarations.drop 267 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 267)).reverse).all
          (fun entry => !((ofString "_decode_witness_node_mpt") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original266 :: declarations.drop 267) =
          (ofString "_decode_witness_node_mpt",[(ofString "db",ShapeHOL.one),(ofString "p",ShapeHOL.one),(ofString "n",ShapeHOL.one),(ofString "mark",ShapeHOL.one)],sourceFunctionBody Guest.guestFn__decode_witness_node_mpt,ShapeHOL.one) ::
            functionsHOL (declarations.drop 267) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original266_eq]
        simp only [Guest.guestFn__decode_witness_node_mpt,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "_decode_witness_node_mpt") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "_decode_witness_node_mpt") (functionsHOL (declarations.drop 267)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "_decode_witness_node_mpt") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_decodeWitnessMpt_lookup

theorem originalRuntimeCode_decodeWitness_lookup :
    originalRuntimeCode.lookup (ofString "_decode_witness_node") =
      some ([(ofString "db",.one),(ofString "p",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn__decode_witness_node,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "_decode_witness_node") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "_decode_witness_node") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "_decode_witness_node")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 267 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original267 :: declarations.drop 268 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 268)).reverse).all
          (fun entry => !((ofString "_decode_witness_node") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original267 :: declarations.drop 268) =
          (ofString "_decode_witness_node",[(ofString "db",ShapeHOL.one),(ofString "p",ShapeHOL.one),(ofString "n",ShapeHOL.one)],sourceFunctionBody Guest.guestFn__decode_witness_node,ShapeHOL.one) ::
            functionsHOL (declarations.drop 268) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original267_eq]
        simp only [Guest.guestFn__decode_witness_node,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "_decode_witness_node") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "_decode_witness_node") (functionsHOL (declarations.drop 268)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "_decode_witness_node") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_decodeWitness_lookup

end InitECandidate.Runtime
