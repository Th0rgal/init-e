import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.VmFn_trap_with

import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 8000000
theorem vmLookup_scratch_alloc :
    originalRuntimeCode.lookup (ofString "scratch_alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_scratch_alloc,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "scratch_alloc") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "scratch_alloc") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "scratch_alloc")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 14 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original14 :: declarations.drop 15 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 15)).reverse).all
          (fun entry => !((ofString "scratch_alloc") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original14 :: declarations.drop 15) =
          (ofString "scratch_alloc",[(ofString "n",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_scratch_alloc,ShapeHOL.one) ::
            functionsHOL (declarations.drop 15) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original14_eq]
        simp only [Guest.guestFn_scratch_alloc,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "scratch_alloc") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "scratch_alloc") (functionsHOL (declarations.drop 15)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "scratch_alloc") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_scratch_alloc

theorem vmBound_scratch_alloc : FunBounded (ofString "scratch_alloc") 2 :=
  ⟨_,_,_,vmLookup_scratch_alloc,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [vmBound_trap_with]
    · decide⟩

#print axioms vmBound_scratch_alloc
end InitECandidate.Runtime
