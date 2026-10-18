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
theorem vmLookup_ripemd160_init :
    originalRuntimeCode.lookup (ofString "ripemd160_init") =
      some ([],sourceFunctionBody Guest.guestFn_ripemd160_init,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "ripemd160_init") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "ripemd160_init") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "ripemd160_init")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 615 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original615 :: declarations.drop 616 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 616)).reverse).all
          (fun entry => !((ofString "ripemd160_init") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original615 :: declarations.drop 616) =
          (ofString "ripemd160_init",[],sourceFunctionBody Guest.guestFn_ripemd160_init,ShapeHOL.one) ::
            functionsHOL (declarations.drop 616) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original615_eq]
        simp only [Guest.guestFn_ripemd160_init,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "ripemd160_init") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "ripemd160_init") (functionsHOL (declarations.drop 616)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "ripemd160_init") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_ripemd160_init

theorem vmBound_ripemd160_init : FunBounded (ofString "ripemd160_init") 8 :=
  ⟨_,_,_,vmLookup_ripemd160_init,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound []
    · decide⟩

#print axioms vmBound_ripemd160_init
end InitECandidate.Runtime
