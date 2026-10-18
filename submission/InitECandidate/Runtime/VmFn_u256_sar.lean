import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.VmFn_u256_or
import InitECandidate.Runtime.VmFn_u256_shl
import InitECandidate.Runtime.VmFn_u256_shr

import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 8000000
theorem vmLookup_u256_sar :
    originalRuntimeCode.lookup (ofString "u256_sar") =
      some ([(ofString "a",.comb [.one,.one,.one,.one]),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_u256_sar,.comb [.one,.one,.one,.one]) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "u256_sar") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "u256_sar") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "u256_sar")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 84 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original84 :: declarations.drop 85 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 85)).reverse).all
          (fun entry => !((ofString "u256_sar") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original84 :: declarations.drop 85) =
          (ofString "u256_sar",[(ofString "a",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "n",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_u256_sar,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 85) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original84_eq]
        simp only [Guest.guestFn_u256_sar,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "u256_sar") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "u256_sar") (functionsHOL (declarations.drop 85)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "u256_sar") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_u256_sar

theorem vmBound_u256_sar : FunBounded (ofString "u256_sar") 3 :=
  ⟨_,_,_,vmLookup_u256_sar,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [vmBound_u256_or,vmBound_u256_shl,vmBound_u256_shr]
    · decide⟩

#print axioms vmBound_u256_sar
end InitECandidate.Runtime
