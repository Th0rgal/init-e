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
theorem vmLookup_frame_state_gas_used :
    originalRuntimeCode.lookup (ofString "frame_state_gas_used") =
      some ([(ofString "e",.one)],sourceFunctionBody Guest.guestFn_frame_state_gas_used,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "frame_state_gas_used") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "frame_state_gas_used") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "frame_state_gas_used")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 454 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original454 :: declarations.drop 455 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 455)).reverse).all
          (fun entry => !((ofString "frame_state_gas_used") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original454 :: declarations.drop 455) =
          (ofString "frame_state_gas_used",[(ofString "e",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_frame_state_gas_used,ShapeHOL.one) ::
            functionsHOL (declarations.drop 455) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original454_eq]
        simp only [Guest.guestFn_frame_state_gas_used,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "frame_state_gas_used") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "frame_state_gas_used") (functionsHOL (declarations.drop 455)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "frame_state_gas_used") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_frame_state_gas_used

theorem vmBound_frame_state_gas_used : FunBounded (ofString "frame_state_gas_used") 0 :=
  ⟨_,_,_,vmLookup_frame_state_gas_used,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound []
    · decide⟩

#print axioms vmBound_frame_state_gas_used
end InitECandidate.Runtime
