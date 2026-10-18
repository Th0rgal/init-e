import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.VmFn_extend_memory_cost1

import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 8000000
theorem vmLookup_extend_memory_cost2 :
    originalRuntimeCode.lookup (ofString "extend_memory_cost2") =
      some ([(ofString "s1",.comb [.one,.one,.one,.one]),(ofString "n1",.comb [.one,.one,.one,.one]),(ofString "s2",.comb [.one,.one,.one,.one]),(ofString "n2",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_extend_memory_cost2,.comb [.one,.one]) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "extend_memory_cost2") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "extend_memory_cost2") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "extend_memory_cost2")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 462 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original462 :: declarations.drop 463 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 463)).reverse).all
          (fun entry => !((ofString "extend_memory_cost2") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original462 :: declarations.drop 463) =
          (ofString "extend_memory_cost2",[(ofString "s1",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "n1",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "s2",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "n2",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_extend_memory_cost2,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 463) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original462_eq]
        simp only [Guest.guestFn_extend_memory_cost2,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "extend_memory_cost2") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "extend_memory_cost2") (functionsHOL (declarations.drop 463)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "extend_memory_cost2") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_extend_memory_cost2

theorem vmBound_extend_memory_cost2 : FunBounded (ofString "extend_memory_cost2") 42 :=
  ⟨_,_,_,vmLookup_extend_memory_cost2,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [vmBound_extend_memory_cost1]
    · decide⟩

#print axioms vmBound_extend_memory_cost2
end InitECandidate.Runtime
