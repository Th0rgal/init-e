import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.VmFn_ceil32

import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 8000000
theorem vmLookup_words_of :
    originalRuntimeCode.lookup (ofString "words_of") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_words_of,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "words_of") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "words_of") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "words_of")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 446 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original446 :: declarations.drop 447 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 447)).reverse).all
          (fun entry => !((ofString "words_of") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original446 :: declarations.drop 447) =
          (ofString "words_of",[(ofString "n",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_words_of,ShapeHOL.one) ::
            functionsHOL (declarations.drop 447) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original446_eq]
        simp only [Guest.guestFn_words_of,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "words_of") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "words_of") (functionsHOL (declarations.drop 447)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "words_of") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_words_of

theorem vmBound_words_of : FunBounded (ofString "words_of") 2 :=
  ⟨_,_,_,vmLookup_words_of,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [vmBound_ceil32]
    · decide⟩

#print axioms vmBound_words_of
end InitECandidate.Runtime
