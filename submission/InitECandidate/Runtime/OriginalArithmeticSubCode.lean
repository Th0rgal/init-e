import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_opSub_lookup :
    originalRuntimeCode.lookup (ofString "op_sub") =
      some ([],sourceFunctionBody Guest.guestFn_op_sub,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "op_sub") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "op_sub") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "op_sub")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 480 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original480 :: declarations.drop 481 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 481)).reverse).all
          (fun entry => !((ofString "op_sub") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original480 :: declarations.drop 481) =
          (ofString "op_sub",[],sourceFunctionBody Guest.guestFn_op_sub,ShapeHOL.one) ::
            functionsHOL (declarations.drop 481) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original480_eq]
        simp only [Guest.guestFn_op_sub,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "op_sub") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "op_sub") (functionsHOL (declarations.drop 481)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "op_sub") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]


#print axioms originalRuntimeCode_opSub_lookup
end InitECandidate.Runtime
