import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.VmFn_min

import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 8000000
theorem vmLookup_credit_state_gas_refund :
    originalRuntimeCode.lookup (ofString "credit_state_gas_refund") =
      some ([(ofString "amount",.one)],sourceFunctionBody Guest.guestFn_credit_state_gas_refund,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "credit_state_gas_refund") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "credit_state_gas_refund") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "credit_state_gas_refund")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 453 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original453 :: declarations.drop 454 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 454)).reverse).all
          (fun entry => !((ofString "credit_state_gas_refund") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original453 :: declarations.drop 454) =
          (ofString "credit_state_gas_refund",[(ofString "amount",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_credit_state_gas_refund,ShapeHOL.one) ::
            functionsHOL (declarations.drop 454) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original453_eq]
        simp only [Guest.guestFn_credit_state_gas_refund,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "credit_state_gas_refund") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "credit_state_gas_refund") (functionsHOL (declarations.drop 454)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "credit_state_gas_refund") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_credit_state_gas_refund

theorem vmBound_credit_state_gas_refund : FunBounded (ofString "credit_state_gas_refund") 1 :=
  ⟨_,_,_,vmLookup_credit_state_gas_refund,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [vmBound_min]
    · decide⟩

#print axioms vmBound_credit_state_gas_refund
end InitECandidate.Runtime
