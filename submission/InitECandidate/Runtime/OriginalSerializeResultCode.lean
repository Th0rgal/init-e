import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_serializeResult_lookup :
    originalRuntimeCode.lookup (ofString "serialize_result") =
      some ([(ofString "out",.one),(ofString "root",.one),(ofString "succ",.one),(ofString "chain_id",.one),(ofString "schema_id",.one)],sourceFunctionBody Guest.guestFn_serialize_result,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "serialize_result") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "serialize_result") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "serialize_result")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 222 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original222 :: declarations.drop 223 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 223)).reverse).all
          (fun entry => !((ofString "serialize_result") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original222 :: declarations.drop 223) =
          (ofString "serialize_result",[(ofString "out",ShapeHOL.one),(ofString "root",ShapeHOL.one),(ofString "succ",ShapeHOL.one),(ofString "chain_id",ShapeHOL.one),(ofString "schema_id",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_serialize_result,ShapeHOL.one) ::
            functionsHOL (declarations.drop 223) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original222_eq]
        simp only [Guest.guestFn_serialize_result,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "serialize_result") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "serialize_result") (functionsHOL (declarations.drop 223)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "serialize_result") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_serializeResult_lookup

end InitECandidate.Runtime
