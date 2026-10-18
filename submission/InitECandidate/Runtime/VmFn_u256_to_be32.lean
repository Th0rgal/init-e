import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.VmFn_bswap64
import InitECandidate.Runtime.VmFn_st_be64

import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 8000000
theorem vmLookup_u256_to_be32 :
    originalRuntimeCode.lookup (ofString "u256_to_be32") =
      some ([(ofString "a",.comb [.one,.one,.one,.one]),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_u256_to_be32,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "u256_to_be32") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "u256_to_be32") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "u256_to_be32")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 88 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original88 :: declarations.drop 89 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 89)).reverse).all
          (fun entry => !((ofString "u256_to_be32") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original88 :: declarations.drop 89) =
          (ofString "u256_to_be32",[(ofString "a",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "out",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_u256_to_be32,ShapeHOL.one) ::
            functionsHOL (declarations.drop 89) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original88_eq]
        simp only [Guest.guestFn_u256_to_be32,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "u256_to_be32") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "u256_to_be32") (functionsHOL (declarations.drop 89)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "u256_to_be32") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_u256_to_be32

theorem vmBound_u256_to_be32 : FunBounded (ofString "u256_to_be32") 20 :=
  ⟨_,_,_,vmLookup_u256_to_be32,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [vmBound_bswap64,vmBound_st_be64]
    · decide⟩

#print axioms vmBound_u256_to_be32
end InitECandidate.Runtime
