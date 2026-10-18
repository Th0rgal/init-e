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
theorem vmLookup_g1_copy :
    originalRuntimeCode.lookup (ofString "g1_copy") =
      some ([(ofString "r",.one),(ofString "p",.one)],sourceFunctionBody Guest.guestFn_g1_copy,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "g1_copy") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "g1_copy") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "g1_copy")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 799 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original799 :: declarations.drop 800 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 800)).reverse).all
          (fun entry => !((ofString "g1_copy") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original799 :: declarations.drop 800) =
          (ofString "g1_copy",[(ofString "r",ShapeHOL.one),(ofString "p",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_g1_copy,ShapeHOL.one) ::
            functionsHOL (declarations.drop 800) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original799_eq]
        simp only [Guest.guestFn_g1_copy,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "g1_copy") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "g1_copy") (functionsHOL (declarations.drop 800)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "g1_copy") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_g1_copy

theorem vmBound_g1_copy : FunBounded (ofString "g1_copy") 33 :=
  ⟨_,_,_,vmLookup_g1_copy,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound []
    · decide⟩

#print axioms vmBound_g1_copy
end InitECandidate.Runtime
