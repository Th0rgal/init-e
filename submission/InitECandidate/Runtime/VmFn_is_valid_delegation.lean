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
theorem vmLookup_is_valid_delegation :
    originalRuntimeCode.lookup (ofString "is_valid_delegation") =
      some ([(ofString "code",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_is_valid_delegation,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "is_valid_delegation") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "is_valid_delegation") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "is_valid_delegation")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 449 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original449 :: declarations.drop 450 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 450)).reverse).all
          (fun entry => !((ofString "is_valid_delegation") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original449 :: declarations.drop 450) =
          (ofString "is_valid_delegation",[(ofString "code",ShapeHOL.one),(ofString "n",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_is_valid_delegation,ShapeHOL.one) ::
            functionsHOL (declarations.drop 450) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original449_eq]
        simp only [Guest.guestFn_is_valid_delegation,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "is_valid_delegation") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "is_valid_delegation") (functionsHOL (declarations.drop 450)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "is_valid_delegation") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_is_valid_delegation

theorem vmBound_is_valid_delegation : FunBounded (ofString "is_valid_delegation") 0 :=
  ⟨_,_,_,vmLookup_is_valid_delegation,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound []
    · decide⟩

#print axioms vmBound_is_valid_delegation
end InitECandidate.Runtime
