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
theorem vmLookup_scratch_mark :
    originalRuntimeCode.lookup (ofString "scratch_mark") =
      some ([],sourceFunctionBody Guest.guestFn_scratch_mark,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "scratch_mark") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "scratch_mark") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "scratch_mark")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 15 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original15 :: declarations.drop 16 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 16)).reverse).all
          (fun entry => !((ofString "scratch_mark") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original15 :: declarations.drop 16) =
          (ofString "scratch_mark",[],sourceFunctionBody Guest.guestFn_scratch_mark,ShapeHOL.one) ::
            functionsHOL (declarations.drop 16) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original15_eq]
        simp only [Guest.guestFn_scratch_mark,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "scratch_mark") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "scratch_mark") (functionsHOL (declarations.drop 16)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "scratch_mark") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_scratch_mark

theorem vmBound_scratch_mark : FunBounded (ofString "scratch_mark") 0 :=
  ⟨_,_,_,vmLookup_scratch_mark,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound []
    · decide⟩

#print axioms vmBound_scratch_mark
end InitECandidate.Runtime
