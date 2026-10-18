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
theorem vmLookup_node_invalidate :
    originalRuntimeCode.lookup (ofString "node_invalidate") =
      some ([(ofString "nd",.one)],sourceFunctionBody Guest.guestFn_node_invalidate,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "node_invalidate") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "node_invalidate") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "node_invalidate")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 262 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original262 :: declarations.drop 263 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 263)).reverse).all
          (fun entry => !((ofString "node_invalidate") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original262 :: declarations.drop 263) =
          (ofString "node_invalidate",[(ofString "nd",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_node_invalidate,ShapeHOL.one) ::
            functionsHOL (declarations.drop 263) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original262_eq]
        simp only [Guest.guestFn_node_invalidate,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "node_invalidate") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "node_invalidate") (functionsHOL (declarations.drop 263)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "node_invalidate") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_node_invalidate

theorem vmBound_node_invalidate : FunBounded (ofString "node_invalidate") 0 :=
  ⟨_,_,_,vmLookup_node_invalidate,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound []
    · decide⟩

#print axioms vmBound_node_invalidate
end InitECandidate.Runtime
