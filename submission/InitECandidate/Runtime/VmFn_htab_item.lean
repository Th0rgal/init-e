import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.VmFn_htab_slot

import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 8000000
theorem vmLookup_htab_item :
    originalRuntimeCode.lookup (ofString "htab_item") =
      some ([(ofString "t",.one),(ofString "ordinal",.one)],sourceFunctionBody Guest.guestFn_htab_item,.comb [.one,.one,.one]) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "htab_item") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "htab_item") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "htab_item")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 143 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original143 :: declarations.drop 144 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 144)).reverse).all
          (fun entry => !((ofString "htab_item") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original143 :: declarations.drop 144) =
          (ofString "htab_item",[(ofString "t",ShapeHOL.one),(ofString "ordinal",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_htab_item,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 144) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original143_eq]
        simp only [Guest.guestFn_htab_item,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "htab_item") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "htab_item") (functionsHOL (declarations.drop 144)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "htab_item") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_htab_item

theorem vmBound_htab_item : FunBounded (ofString "htab_item") 1 :=
  ⟨_,_,_,vmLookup_htab_item,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [vmBound_htab_slot]
    · decide⟩

#print axioms vmBound_htab_item
end InitECandidate.Runtime
