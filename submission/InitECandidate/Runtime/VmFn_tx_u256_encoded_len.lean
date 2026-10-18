import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.VmFn_u256_byte_length

import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 8000000
theorem vmLookup_tx_u256_encoded_len :
    originalRuntimeCode.lookup (ofString "tx_u256_encoded_len") =
      some ([(ofString "v",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_tx_u256_encoded_len,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "tx_u256_encoded_len") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "tx_u256_encoded_len") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "tx_u256_encoded_len")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 322 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original322 :: declarations.drop 323 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 323)).reverse).all
          (fun entry => !((ofString "tx_u256_encoded_len") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original322 :: declarations.drop 323) =
          (ofString "tx_u256_encoded_len",[(ofString "v",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_tx_u256_encoded_len,ShapeHOL.one) ::
            functionsHOL (declarations.drop 323) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original322_eq]
        simp only [Guest.guestFn_tx_u256_encoded_len,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "tx_u256_encoded_len") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "tx_u256_encoded_len") (functionsHOL (declarations.drop 323)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "tx_u256_encoded_len") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_tx_u256_encoded_len

theorem vmBound_tx_u256_encoded_len : FunBounded (ofString "tx_u256_encoded_len") 6 :=
  ⟨_,_,_,vmLookup_tx_u256_encoded_len,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [vmBound_u256_byte_length]
    · decide⟩

#print axioms vmBound_tx_u256_encoded_len
end InitECandidate.Runtime
