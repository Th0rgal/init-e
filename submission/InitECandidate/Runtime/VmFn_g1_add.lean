import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.VmFn_bls_fp_add
import InitECandidate.Runtime.VmFn_bls_fp_eq
import InitECandidate.Runtime.VmFn_bls_fp_is_zero
import InitECandidate.Runtime.VmFn_bls_fp_mul
import InitECandidate.Runtime.VmFn_bls_fp_sqr
import InitECandidate.Runtime.VmFn_bls_fp_sub
import InitECandidate.Runtime.VmFn_bls_g1_accel_init
import InitECandidate.Runtime.VmFn_g1_copy
import InitECandidate.Runtime.VmFn_g1_double
import InitECandidate.Runtime.VmFn_g1_set_inf

import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 8000000
theorem vmLookup_g1_add :
    originalRuntimeCode.lookup (ofString "g1_add") =
      some ([(ofString "r",.one),(ofString "p1",.one),(ofString "p2",.one)],sourceFunctionBody Guest.guestFn_g1_add,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "g1_add") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "g1_add") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "g1_add")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 802 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original802 :: declarations.drop 803 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 803)).reverse).all
          (fun entry => !((ofString "g1_add") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original802 :: declarations.drop 803) =
          (ofString "g1_add",[(ofString "r",ShapeHOL.one),(ofString "p1",ShapeHOL.one),(ofString "p2",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_g1_add,ShapeHOL.one) ::
            functionsHOL (declarations.drop 803) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original802_eq]
        simp only [Guest.guestFn_g1_add,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "g1_add") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "g1_add") (functionsHOL (declarations.drop 803)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "g1_add") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_g1_add

theorem vmBound_g1_add : FunBounded (ofString "g1_add") 1773 :=
  ⟨_,_,_,vmLookup_g1_add,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [vmBound_bls_fp_add,vmBound_bls_fp_eq,vmBound_bls_fp_is_zero,vmBound_bls_fp_mul,vmBound_bls_fp_sqr,vmBound_bls_fp_sub,vmBound_bls_g1_accel_init,vmBound_g1_copy,vmBound_g1_double,vmBound_g1_set_inf]
    · decide⟩

#print axioms vmBound_g1_add
end InitECandidate.Runtime
