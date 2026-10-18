import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_decodeBytesList_lookup :
    originalRuntimeCode.lookup (ofString "decode_bytes_list") =
      some ([(ofString "p",.one),(ofString "len",.one),(ofString "lim",.one),(ofString "maxb",.one)],sourceFunctionBody Guest.guestFn_decode_bytes_list,.comb [.one,.one]) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "decode_bytes_list") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "decode_bytes_list") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "decode_bytes_list")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 209 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original209 :: declarations.drop 210 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 210)).reverse).all
          (fun entry => !((ofString "decode_bytes_list") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original209 :: declarations.drop 210) =
          (ofString "decode_bytes_list",[(ofString "p",ShapeHOL.one),(ofString "len",ShapeHOL.one),(ofString "lim",ShapeHOL.one),(ofString "maxb",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_decode_bytes_list,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 210) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original209_eq]
        simp only [Guest.guestFn_decode_bytes_list,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "decode_bytes_list") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "decode_bytes_list") (functionsHOL (declarations.drop 210)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "decode_bytes_list") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_decodeBytesList_lookup

end InitECandidate.Runtime
