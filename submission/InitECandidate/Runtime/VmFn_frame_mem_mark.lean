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
theorem vmLookup_frame_mem_mark :
    originalRuntimeCode.lookup (ofString "frame_mem_mark") =
      some ([],sourceFunctionBody Guest.guestFn_frame_mem_mark,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "frame_mem_mark") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "frame_mem_mark") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "frame_mem_mark")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 12 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original12 :: declarations.drop 13 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 13)).reverse).all
          (fun entry => !((ofString "frame_mem_mark") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original12 :: declarations.drop 13) =
          (ofString "frame_mem_mark",[],sourceFunctionBody Guest.guestFn_frame_mem_mark,ShapeHOL.one) ::
            functionsHOL (declarations.drop 13) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original12_eq]
        simp only [Guest.guestFn_frame_mem_mark,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "frame_mem_mark") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "frame_mem_mark") (functionsHOL (declarations.drop 13)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "frame_mem_mark") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_frame_mem_mark

theorem vmBound_frame_mem_mark : FunBounded (ofString "frame_mem_mark") 0 :=
  ⟨_,_,_,vmLookup_frame_mem_mark,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound []
    · decide⟩

#print axioms vmBound_frame_mem_mark
end InitECandidate.Runtime
