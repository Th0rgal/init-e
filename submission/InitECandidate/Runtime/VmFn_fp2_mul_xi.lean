import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.VmFn_bls_fp_add
import InitECandidate.Runtime.VmFn_bls_fp_sub

import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 8000000
theorem vmLookup_fp2_mul_xi :
    originalRuntimeCode.lookup (ofString "fp2_mul_xi") =
      some ([(ofString "r",.one),(ofString "a",.one)],sourceFunctionBody Guest.guestFn_fp2_mul_xi,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "fp2_mul_xi") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "fp2_mul_xi") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "fp2_mul_xi")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 768 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original768 :: declarations.drop 769 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 769)).reverse).all
          (fun entry => !((ofString "fp2_mul_xi") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original768 :: declarations.drop 769) =
          (ofString "fp2_mul_xi",[(ofString "r",ShapeHOL.one),(ofString "a",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_fp2_mul_xi,ShapeHOL.one) ::
            functionsHOL (declarations.drop 769) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original768_eq]
        simp only [Guest.guestFn_fp2_mul_xi,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "fp2_mul_xi") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "fp2_mul_xi") (functionsHOL (declarations.drop 769)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "fp2_mul_xi") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_fp2_mul_xi

theorem vmBound_fp2_mul_xi : FunBounded (ofString "fp2_mul_xi") 6 :=
  ⟨_,_,_,vmLookup_fp2_mul_xi,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [vmBound_bls_fp_add,vmBound_bls_fp_sub]
    · decide⟩

#print axioms vmBound_fp2_mul_xi
end InitECandidate.Runtime
