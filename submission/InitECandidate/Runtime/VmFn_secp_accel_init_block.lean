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
theorem vmLookup_secp_accel_init_block :
    originalRuntimeCode.lookup (ofString "secp_accel_init_block") =
      some ([(ofString "base",.one),(ofString "modulus",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_secp_accel_init_block,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "secp_accel_init_block") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "secp_accel_init_block") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "secp_accel_init_block")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 148 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original148 :: declarations.drop 149 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 149)).reverse).all
          (fun entry => !((ofString "secp_accel_init_block") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original148 :: declarations.drop 149) =
          (ofString "secp_accel_init_block",[(ofString "base",ShapeHOL.one),(ofString "modulus",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_secp_accel_init_block,ShapeHOL.one) ::
            functionsHOL (declarations.drop 149) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original148_eq]
        simp only [Guest.guestFn_secp_accel_init_block,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "secp_accel_init_block") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "secp_accel_init_block") (functionsHOL (declarations.drop 149)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "secp_accel_init_block") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_secp_accel_init_block

theorem vmBound_secp_accel_init_block : FunBounded (ofString "secp_accel_init_block") 0 :=
  ⟨_,_,_,vmLookup_secp_accel_init_block,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound []
    · decide⟩

#print axioms vmBound_secp_accel_init_block
end InitECandidate.Runtime
