import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.VmFn_secp_accel_init_block

import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 8000000
theorem vmLookup_secp256k1_init :
    originalRuntimeCode.lookup (ofString "secp256k1_init") =
      some ([],sourceFunctionBody Guest.guestFn_secp256k1_init,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "secp256k1_init") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "secp256k1_init") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "secp256k1_init")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 149 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original149 :: declarations.drop 150 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 150)).reverse).all
          (fun entry => !((ofString "secp256k1_init") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original149 :: declarations.drop 150) =
          (ofString "secp256k1_init",[],sourceFunctionBody Guest.guestFn_secp256k1_init,ShapeHOL.one) ::
            functionsHOL (declarations.drop 150) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original149_eq]
        simp only [Guest.guestFn_secp256k1_init,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "secp256k1_init") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "secp256k1_init") (functionsHOL (declarations.drop 150)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "secp256k1_init") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_secp256k1_init

theorem vmBound_secp256k1_init : FunBounded (ofString "secp256k1_init") 4 :=
  ⟨_,_,_,vmLookup_secp256k1_init,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [vmBound_secp_accel_init_block]
    · decide⟩

#print axioms vmBound_secp256k1_init
end InitECandidate.Runtime
