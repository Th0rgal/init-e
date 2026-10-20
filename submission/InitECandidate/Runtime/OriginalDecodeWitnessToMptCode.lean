import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_decodeWitnessToMpt_lookup :
    originalRuntimeCode.lookup (ofString "decode_witness_to_mpt") =
      some ([(ofString "db",.one),(ofString "root_hash",.one)],sourceFunctionBody Guest.guestFn_decode_witness_to_mpt,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "decode_witness_to_mpt") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "decode_witness_to_mpt") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "decode_witness_to_mpt")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 268 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original268 :: declarations.drop 269 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 269)).reverse).all
          (fun entry => !((ofString "decode_witness_to_mpt") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original268 :: declarations.drop 269) =
          (ofString "decode_witness_to_mpt",[(ofString "db",ShapeHOL.one),(ofString "root_hash",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_decode_witness_to_mpt,ShapeHOL.one) ::
            functionsHOL (declarations.drop 269) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original268_eq]
        simp only [Guest.guestFn_decode_witness_to_mpt,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "decode_witness_to_mpt") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "decode_witness_to_mpt") (functionsHOL (declarations.drop 269)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "decode_witness_to_mpt") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_decodeWitnessToMpt_lookup

end InitECandidate.Runtime
