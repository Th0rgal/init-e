import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.VmFn_add_sat

import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 8000000
theorem vmLookup_ceil32 :
    originalRuntimeCode.lookup (ofString "ceil32") =
      some ([(ofString "v",.one)],sourceFunctionBody Guest.guestFn_ceil32,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "ceil32") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "ceil32") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "ceil32")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 445 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original445 :: declarations.drop 446 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 446)).reverse).all
          (fun entry => !((ofString "ceil32") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original445 :: declarations.drop 446) =
          (ofString "ceil32",[(ofString "v",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_ceil32,ShapeHOL.one) ::
            functionsHOL (declarations.drop 446) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original445_eq]
        simp only [Guest.guestFn_ceil32,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "ceil32") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "ceil32") (functionsHOL (declarations.drop 446)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "ceil32") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_ceil32

theorem vmBound_ceil32 : FunBounded (ofString "ceil32") 1 :=
  ⟨_,_,_,vmLookup_ceil32,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [vmBound_add_sat]
    · decide⟩

#print axioms vmBound_ceil32
end InitECandidate.Runtime
