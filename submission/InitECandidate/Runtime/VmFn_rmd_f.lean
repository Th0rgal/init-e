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
theorem vmLookup_rmd_f :
    originalRuntimeCode.lookup (ofString "rmd_f") =
      some ([(ofString "j",.one),(ofString "x",.one),(ofString "y",.one),(ofString "z",.one)],sourceFunctionBody Guest.guestFn_rmd_f,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "rmd_f") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "rmd_f") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "rmd_f")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 616 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original616 :: declarations.drop 617 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 617)).reverse).all
          (fun entry => !((ofString "rmd_f") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original616 :: declarations.drop 617) =
          (ofString "rmd_f",[(ofString "j",ShapeHOL.one),(ofString "x",ShapeHOL.one),(ofString "y",ShapeHOL.one),(ofString "z",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_rmd_f,ShapeHOL.one) ::
            functionsHOL (declarations.drop 617) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original616_eq]
        simp only [Guest.guestFn_rmd_f,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "rmd_f") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "rmd_f") (functionsHOL (declarations.drop 617)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "rmd_f") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_rmd_f

theorem vmBound_rmd_f : FunBounded (ofString "rmd_f") 0 :=
  ⟨_,_,_,vmLookup_rmd_f,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound []
    · decide⟩

#print axioms vmBound_rmd_f
end InitECandidate.Runtime
