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
theorem vmLookup_fp12_copy :
    originalRuntimeCode.lookup (ofString "fp12_copy") =
      some ([(ofString "r",.one),(ofString "a",.one)],sourceFunctionBody Guest.guestFn_fp12_copy,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "fp12_copy") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "fp12_copy") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "fp12_copy")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 782 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original782 :: declarations.drop 783 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 783)).reverse).all
          (fun entry => !((ofString "fp12_copy") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original782 :: declarations.drop 783) =
          (ofString "fp12_copy",[(ofString "r",ShapeHOL.one),(ofString "a",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_fp12_copy,ShapeHOL.one) ::
            functionsHOL (declarations.drop 783) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original782_eq]
        simp only [Guest.guestFn_fp12_copy,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "fp12_copy") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "fp12_copy") (functionsHOL (declarations.drop 783)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "fp12_copy") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_fp12_copy

theorem vmBound_fp12_copy : FunBounded (ofString "fp12_copy") 101 :=
  ⟨_,_,_,vmLookup_fp12_copy,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound []
    · decide⟩

#print axioms vmBound_fp12_copy
end InitECandidate.Runtime
