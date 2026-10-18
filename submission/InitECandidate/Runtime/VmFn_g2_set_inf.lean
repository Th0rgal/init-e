import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.VmFn_fp2_set_one
import InitECandidate.Runtime.VmFn_fp2_set_zero

import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 8000000
theorem vmLookup_g2_set_inf :
    originalRuntimeCode.lookup (ofString "g2_set_inf") =
      some ([(ofString "r",.one)],sourceFunctionBody Guest.guestFn_g2_set_inf,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "g2_set_inf") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "g2_set_inf") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "g2_set_inf")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 809 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original809 :: declarations.drop 810 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 810)).reverse).all
          (fun entry => !((ofString "g2_set_inf") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original809 :: declarations.drop 810) =
          (ofString "g2_set_inf",[(ofString "r",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_g2_set_inf,ShapeHOL.one) ::
            functionsHOL (declarations.drop 810) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original809_eq]
        simp only [Guest.guestFn_g2_set_inf,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "g2_set_inf") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "g2_set_inf") (functionsHOL (declarations.drop 810)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "g2_set_inf") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_g2_set_inf

theorem vmBound_g2_set_inf : FunBounded (ofString "g2_set_inf") 29 :=
  ⟨_,_,_,vmLookup_g2_set_inf,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [vmBound_fp2_set_one,vmBound_fp2_set_zero]
    · decide⟩

#print axioms vmBound_g2_set_inf
end InitECandidate.Runtime
