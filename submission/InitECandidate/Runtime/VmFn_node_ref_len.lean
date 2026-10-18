import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.VmFn_mpt_fail

import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 8000000
theorem vmLookup_node_ref_len :
    originalRuntimeCode.lookup (ofString "node_ref_len") =
      some ([(ofString "child",.one)],sourceFunctionBody Guest.guestFn_node_ref_len,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "node_ref_len") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "node_ref_len") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "node_ref_len")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 290 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original290 :: declarations.drop 291 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 291)).reverse).all
          (fun entry => !((ofString "node_ref_len") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original290 :: declarations.drop 291) =
          (ofString "node_ref_len",[(ofString "child",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_node_ref_len,ShapeHOL.one) ::
            functionsHOL (declarations.drop 291) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original290_eq]
        simp only [Guest.guestFn_node_ref_len,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "node_ref_len") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "node_ref_len") (functionsHOL (declarations.drop 291)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "node_ref_len") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_node_ref_len

theorem vmBound_node_ref_len : FunBounded (ofString "node_ref_len") 1 :=
  ⟨_,_,_,vmLookup_node_ref_len,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [vmBound_mpt_fail]
    · decide⟩

#print axioms vmBound_node_ref_len
end InitECandidate.Runtime
