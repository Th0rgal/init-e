import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.VmFn_charge_gas
import InitECandidate.Runtime.VmFn_code_imm
import InitECandidate.Runtime.VmFn_decode_single
import InitECandidate.Runtime.VmFn_pc_add
import InitECandidate.Runtime.VmFn_stack_swap_positions

import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 8000000
theorem vmLookup_op_swapn :
    originalRuntimeCode.lookup (ofString "op_swapn") =
      some ([],sourceFunctionBody Guest.guestFn_op_swapn,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "op_swapn") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "op_swapn") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "op_swapn")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 524 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original524 :: declarations.drop 525 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 525)).reverse).all
          (fun entry => !((ofString "op_swapn") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original524 :: declarations.drop 525) =
          (ofString "op_swapn",[],sourceFunctionBody Guest.guestFn_op_swapn,ShapeHOL.one) ::
            functionsHOL (declarations.drop 525) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original524_eq]
        simp only [Guest.guestFn_op_swapn,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "op_swapn") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "op_swapn") (functionsHOL (declarations.drop 525)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "op_swapn") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_op_swapn

theorem vmBound_op_swapn : FunBounded (ofString "op_swapn") 5 :=
  ⟨_,_,_,vmLookup_op_swapn,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [vmBound_charge_gas,vmBound_code_imm,vmBound_decode_single,vmBound_pc_add,vmBound_stack_swap_positions]
    · decide⟩

#print axioms vmBound_op_swapn
end InitECandidate.Runtime
