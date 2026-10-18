import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.VmFn_scratch_alloc

import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 8000000
theorem vmLookup_msg_new_scratch :
    originalRuntimeCode.lookup (ofString "msg_new_scratch") =
      some ([],sourceFunctionBody Guest.guestFn_msg_new_scratch,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "msg_new_scratch") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "msg_new_scratch") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "msg_new_scratch")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 469 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original469 :: declarations.drop 470 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 470)).reverse).all
          (fun entry => !((ofString "msg_new_scratch") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original469 :: declarations.drop 470) =
          (ofString "msg_new_scratch",[],sourceFunctionBody Guest.guestFn_msg_new_scratch,ShapeHOL.one) ::
            functionsHOL (declarations.drop 470) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original469_eq]
        simp only [Guest.guestFn_msg_new_scratch,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "msg_new_scratch") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "msg_new_scratch") (functionsHOL (declarations.drop 470)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "msg_new_scratch") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_msg_new_scratch

theorem vmBound_msg_new_scratch : FunBounded (ofString "msg_new_scratch") 41 :=
  ⟨_,_,_,vmLookup_msg_new_scratch,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [vmBound_scratch_alloc]
    · decide⟩

#print axioms vmBound_msg_new_scratch
end InitECandidate.Runtime
