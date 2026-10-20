import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_stackPush_lookup :
    originalRuntimeCode.lookup (ofString "stack_push") =
      some ([(ofString "v",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_stack_push,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "stack_push") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "stack_push") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "stack_push")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 457 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original457 :: declarations.drop 458 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 458)).reverse).all
          (fun entry => !((ofString "stack_push") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original457 :: declarations.drop 458) =
          (ofString "stack_push",[(ofString "v",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_stack_push,ShapeHOL.one) ::
            functionsHOL (declarations.drop 458) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original457_eq]
        simp only [Guest.guestFn_stack_push,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "stack_push") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "stack_push") (functionsHOL (declarations.drop 458)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "stack_push") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]


#print axioms originalRuntimeCode_stackPush_lookup
end InitECandidate.Runtime
