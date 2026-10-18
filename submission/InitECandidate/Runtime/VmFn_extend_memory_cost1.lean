import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.VmFn_add_sat
import InitECandidate.Runtime.VmFn_ceil32
import InitECandidate.Runtime.VmFn_memory_gas_cost
import InitECandidate.Runtime.VmFn_sat_word
import InitECandidate.Runtime.VmFn_u256_is_zero

import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 8000000
theorem vmLookup_extend_memory_cost1 :
    originalRuntimeCode.lookup (ofString "extend_memory_cost1") =
      some ([(ofString "start",.comb [.one,.one,.one,.one]),(ofString "size",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_extend_memory_cost1,.comb [.one,.one]) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "extend_memory_cost1") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "extend_memory_cost1") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "extend_memory_cost1")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 461 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original461 :: declarations.drop 462 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 462)).reverse).all
          (fun entry => !((ofString "extend_memory_cost1") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original461 :: declarations.drop 462) =
          (ofString "extend_memory_cost1",[(ofString "start",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "size",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_extend_memory_cost1,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 462) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original461_eq]
        simp only [Guest.guestFn_extend_memory_cost1,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "extend_memory_cost1") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "extend_memory_cost1") (functionsHOL (declarations.drop 462)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "extend_memory_cost1") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_extend_memory_cost1

theorem vmBound_extend_memory_cost1 : FunBounded (ofString "extend_memory_cost1") 20 :=
  ⟨_,_,_,vmLookup_extend_memory_cost1,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [vmBound_add_sat,vmBound_ceil32,vmBound_memory_gas_cost,vmBound_sat_word,vmBound_u256_is_zero]
    · decide⟩

#print axioms vmBound_extend_memory_cost1
end InitECandidate.Runtime
