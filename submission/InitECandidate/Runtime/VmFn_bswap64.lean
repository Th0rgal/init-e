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
theorem vmLookup_bswap64 :
    originalRuntimeCode.lookup (ofString "bswap64") =
      some ([(ofString "x",.one)],sourceFunctionBody Guest.guestFn_bswap64,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "bswap64") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "bswap64") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "bswap64")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 24 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original24 :: declarations.drop 25 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 25)).reverse).all
          (fun entry => !((ofString "bswap64") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original24 :: declarations.drop 25) =
          (ofString "bswap64",[(ofString "x",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_bswap64,ShapeHOL.one) ::
            functionsHOL (declarations.drop 25) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original24_eq]
        simp only [Guest.guestFn_bswap64,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "bswap64") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "bswap64") (functionsHOL (declarations.drop 25)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "bswap64") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_bswap64

theorem vmBound_bswap64 : FunBounded (ofString "bswap64") 0 :=
  ⟨_,_,_,vmLookup_bswap64,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound []
    · decide⟩

#print axioms vmBound_bswap64
end InitECandidate.Runtime
