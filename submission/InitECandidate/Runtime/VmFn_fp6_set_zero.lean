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
theorem vmLookup_fp6_set_zero :
    originalRuntimeCode.lookup (ofString "fp6_set_zero") =
      some ([(ofString "r",.one)],sourceFunctionBody Guest.guestFn_fp6_set_zero,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "fp6_set_zero") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "fp6_set_zero") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "fp6_set_zero")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 774 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original774 :: declarations.drop 775 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 775)).reverse).all
          (fun entry => !((ofString "fp6_set_zero") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original774 :: declarations.drop 775) =
          (ofString "fp6_set_zero",[(ofString "r",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_fp6_set_zero,ShapeHOL.one) ::
            functionsHOL (declarations.drop 775) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original774_eq]
        simp only [Guest.guestFn_fp6_set_zero,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "fp6_set_zero") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "fp6_set_zero") (functionsHOL (declarations.drop 775)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "fp6_set_zero") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_fp6_set_zero

theorem vmBound_fp6_set_zero : FunBounded (ofString "fp6_set_zero") 56 :=
  ⟨_,_,_,vmLookup_fp6_set_zero,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound []
    · decide⟩

#print axioms vmBound_fp6_set_zero
end InitECandidate.Runtime
