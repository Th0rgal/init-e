import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.VmFn_is_valid_delegation

import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 8000000
theorem vmLookup_get_delegated_code_address :
    originalRuntimeCode.lookup (ofString "get_delegated_code_address") =
      some ([(ofString "code",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_get_delegated_code_address,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "get_delegated_code_address") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "get_delegated_code_address") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "get_delegated_code_address")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 574 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original574 :: declarations.drop 575 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 575)).reverse).all
          (fun entry => !((ofString "get_delegated_code_address") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original574 :: declarations.drop 575) =
          (ofString "get_delegated_code_address",[(ofString "code",ShapeHOL.one),(ofString "n",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_get_delegated_code_address,ShapeHOL.one) ::
            functionsHOL (declarations.drop 575) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original574_eq]
        simp only [Guest.guestFn_get_delegated_code_address,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "get_delegated_code_address") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "get_delegated_code_address") (functionsHOL (declarations.drop 575)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "get_delegated_code_address") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_get_delegated_code_address

theorem vmBound_get_delegated_code_address : FunBounded (ofString "get_delegated_code_address") 1 :=
  ⟨_,_,_,vmLookup_get_delegated_code_address,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [vmBound_is_valid_delegation]
    · decide⟩

#print axioms vmBound_get_delegated_code_address
end InitECandidate.Runtime
