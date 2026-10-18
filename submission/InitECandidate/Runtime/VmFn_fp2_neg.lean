import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.VmFn_bls_fp_neg

import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 8000000
theorem vmLookup_fp2_neg :
    originalRuntimeCode.lookup (ofString "fp2_neg") =
      some ([(ofString "r",.one),(ofString "a",.one)],sourceFunctionBody Guest.guestFn_fp2_neg,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "fp2_neg") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "fp2_neg") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "fp2_neg")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 763 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original763 :: declarations.drop 764 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 764)).reverse).all
          (fun entry => !((ofString "fp2_neg") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original763 :: declarations.drop 764) =
          (ofString "fp2_neg",[(ofString "r",ShapeHOL.one),(ofString "a",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_fp2_neg,ShapeHOL.one) ::
            functionsHOL (declarations.drop 764) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original763_eq]
        simp only [Guest.guestFn_fp2_neg,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "fp2_neg") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "fp2_neg") (functionsHOL (declarations.drop 764)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "fp2_neg") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_fp2_neg

theorem vmBound_fp2_neg : FunBounded (ofString "fp2_neg") 6 :=
  ⟨_,_,_,vmLookup_fp2_neg,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [vmBound_bls_fp_neg]
    · decide⟩

#print axioms vmBound_fp2_neg
end InitECandidate.Runtime
