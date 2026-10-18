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
theorem vmLookup_bls_consts_init :
    originalRuntimeCode.lookup (ofString "bls_consts_init") =
      some ([],sourceFunctionBody Guest.guestFn_bls_consts_init,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "bls_consts_init") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "bls_consts_init") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "bls_consts_init")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 721 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original721 :: declarations.drop 722 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 722)).reverse).all
          (fun entry => !((ofString "bls_consts_init") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original721 :: declarations.drop 722) =
          (ofString "bls_consts_init",[],sourceFunctionBody Guest.guestFn_bls_consts_init,ShapeHOL.one) ::
            functionsHOL (declarations.drop 722) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original721_eq]
        simp only [Guest.guestFn_bls_consts_init,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "bls_consts_init") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "bls_consts_init") (functionsHOL (declarations.drop 722)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "bls_consts_init") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_bls_consts_init

theorem vmBound_bls_consts_init : FunBounded (ofString "bls_consts_init") 2 :=
  ⟨_,_,_,vmLookup_bls_consts_init,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound []
    · decide⟩

#print axioms vmBound_bls_consts_init
end InitECandidate.Runtime
