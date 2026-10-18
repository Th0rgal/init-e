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
theorem vmLookup_bls_fp_is_zero :
    originalRuntimeCode.lookup (ofString "bls_fp_is_zero") =
      some ([(ofString "a",.comb [.one,.one,.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_bls_fp_is_zero,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "bls_fp_is_zero") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "bls_fp_is_zero") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "bls_fp_is_zero")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 722 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original722 :: declarations.drop 723 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 723)).reverse).all
          (fun entry => !((ofString "bls_fp_is_zero") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original722 :: declarations.drop 723) =
          (ofString "bls_fp_is_zero",[(ofString "a",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_bls_fp_is_zero,ShapeHOL.one) ::
            functionsHOL (declarations.drop 723) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original722_eq]
        simp only [Guest.guestFn_bls_fp_is_zero,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "bls_fp_is_zero") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "bls_fp_is_zero") (functionsHOL (declarations.drop 723)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "bls_fp_is_zero") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_bls_fp_is_zero

theorem vmBound_bls_fp_is_zero : FunBounded (ofString "bls_fp_is_zero") 0 :=
  ⟨_,_,_,vmLookup_bls_fp_is_zero,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound []
    · decide⟩

#print axioms vmBound_bls_fp_is_zero
end InitECandidate.Runtime
