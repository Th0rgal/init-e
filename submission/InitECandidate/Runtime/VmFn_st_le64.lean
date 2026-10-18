import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.VmFn_st_le32

import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 8000000
theorem vmLookup_st_le64 :
    originalRuntimeCode.lookup (ofString "st_le64") =
      some ([(ofString "p",.one),(ofString "v",.one)],sourceFunctionBody Guest.guestFn_st_le64,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "st_le64") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "st_le64") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "st_le64")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 27 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original27 :: declarations.drop 28 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 28)).reverse).all
          (fun entry => !((ofString "st_le64") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original27 :: declarations.drop 28) =
          (ofString "st_le64",[(ofString "p",ShapeHOL.one),(ofString "v",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_st_le64,ShapeHOL.one) ::
            functionsHOL (declarations.drop 28) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original27_eq]
        simp only [Guest.guestFn_st_le64,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "st_le64") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "st_le64") (functionsHOL (declarations.drop 28)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "st_le64") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_st_le64

theorem vmBound_st_le64 : FunBounded (ofString "st_le64") 2 :=
  ⟨_,_,_,vmLookup_st_le64,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [vmBound_st_le32]
    · decide⟩

#print axioms vmBound_st_le64
end InitECandidate.Runtime
