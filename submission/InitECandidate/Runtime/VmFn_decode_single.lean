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
theorem vmLookup_decode_single :
    originalRuntimeCode.lookup (ofString "decode_single") =
      some ([(ofString "x",.one)],sourceFunctionBody Guest.guestFn_decode_single,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "decode_single") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "decode_single") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "decode_single")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 522 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original522 :: declarations.drop 523 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 523)).reverse).all
          (fun entry => !((ofString "decode_single") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original522 :: declarations.drop 523) =
          (ofString "decode_single",[(ofString "x",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_decode_single,ShapeHOL.one) ::
            functionsHOL (declarations.drop 523) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original522_eq]
        simp only [Guest.guestFn_decode_single,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "decode_single") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "decode_single") (functionsHOL (declarations.drop 523)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "decode_single") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_decode_single

theorem vmBound_decode_single : FunBounded (ofString "decode_single") 0 :=
  ⟨_,_,_,vmLookup_decode_single,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound []
    · decide⟩

#print axioms vmBound_decode_single
end InitECandidate.Runtime
