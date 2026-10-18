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
theorem vmLookup_nlz32 :
    originalRuntimeCode.lookup (ofString "nlz32") =
      some ([(ofString "x",.one)],sourceFunctionBody Guest.guestFn_nlz32,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "nlz32") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "nlz32") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "nlz32")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 63 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original63 :: declarations.drop 64 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 64)).reverse).all
          (fun entry => !((ofString "nlz32") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original63 :: declarations.drop 64) =
          (ofString "nlz32",[(ofString "x",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_nlz32,ShapeHOL.one) ::
            functionsHOL (declarations.drop 64) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original63_eq]
        simp only [Guest.guestFn_nlz32,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "nlz32") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "nlz32") (functionsHOL (declarations.drop 64)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "nlz32") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_nlz32

theorem vmBound_nlz32 : FunBounded (ofString "nlz32") 0 :=
  ⟨_,_,_,vmLookup_nlz32,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound []
    · decide⟩

#print axioms vmBound_nlz32
end InitECandidate.Runtime
