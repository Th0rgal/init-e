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
theorem vmLookup_sk_make :
    originalRuntimeCode.lookup (ofString "sk_make") =
      some ([(ofString "addr",.one),(ofString "key",.one)],sourceFunctionBody Guest.guestFn_sk_make,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "sk_make") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "sk_make") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "sk_make")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 363 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original363 :: declarations.drop 364 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 364)).reverse).all
          (fun entry => !((ofString "sk_make") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original363 :: declarations.drop 364) =
          (ofString "sk_make",[(ofString "addr",ShapeHOL.one),(ofString "key",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_sk_make,ShapeHOL.one) ::
            functionsHOL (declarations.drop 364) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original363_eq]
        simp only [Guest.guestFn_sk_make,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "sk_make") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "sk_make") (functionsHOL (declarations.drop 364)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "sk_make") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_sk_make

theorem vmBound_sk_make : FunBounded (ofString "sk_make") 29 :=
  ⟨_,_,_,vmLookup_sk_make,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound []
    · decide⟩

#print axioms vmBound_sk_make
end InitECandidate.Runtime
