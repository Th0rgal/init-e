import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.AllocationInitializersBound

import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 8000000
theorem vmLookup_incorporate_child_on_error :
    originalRuntimeCode.lookup (ofString "incorporate_child_on_error") =
      some ([(ofString "child",.one)],sourceFunctionBody Guest.guestFn_incorporate_child_on_error,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "incorporate_child_on_error") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "incorporate_child_on_error") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "incorporate_child_on_error")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 594 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original594 :: declarations.drop 595 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 595)).reverse).all
          (fun entry => !((ofString "incorporate_child_on_error") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original594 :: declarations.drop 595) =
          (ofString "incorporate_child_on_error",[(ofString "child",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_incorporate_child_on_error,ShapeHOL.one) ::
            functionsHOL (declarations.drop 595) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original594_eq]
        simp only [Guest.guestFn_incorporate_child_on_error,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "incorporate_child_on_error") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "incorporate_child_on_error") (functionsHOL (declarations.drop 595)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "incorporate_child_on_error") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_incorporate_child_on_error

theorem vmBound_incorporate_child_on_error : FunBounded (ofString "incorporate_child_on_error") 0 :=
  ⟨_,_,_,vmLookup_incorporate_child_on_error,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound []
    · decide⟩

#print axioms vmBound_incorporate_child_on_error
end InitECandidate.Runtime
