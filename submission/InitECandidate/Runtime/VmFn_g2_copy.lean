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
theorem vmLookup_g2_copy :
    originalRuntimeCode.lookup (ofString "g2_copy") =
      some ([(ofString "r",.one),(ofString "p",.one)],sourceFunctionBody Guest.guestFn_g2_copy,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "g2_copy") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "g2_copy") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "g2_copy")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 811 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original811 :: declarations.drop 812 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 812)).reverse).all
          (fun entry => !((ofString "g2_copy") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original811 :: declarations.drop 812) =
          (ofString "g2_copy",[(ofString "r",ShapeHOL.one),(ofString "p",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_g2_copy,ShapeHOL.one) ::
            functionsHOL (declarations.drop 812) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original811_eq]
        simp only [Guest.guestFn_g2_copy,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "g2_copy") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "g2_copy") (functionsHOL (declarations.drop 812)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "g2_copy") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_g2_copy

theorem vmBound_g2_copy : FunBounded (ofString "g2_copy") 56 :=
  ⟨_,_,_,vmLookup_g2_copy,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound []
    · decide⟩

#print axioms vmBound_g2_copy
end InitECandidate.Runtime
