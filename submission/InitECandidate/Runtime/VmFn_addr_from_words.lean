import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.VmFn_st_be32
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
theorem vmLookup_addr_from_words :
    originalRuntimeCode.lookup (ofString "addr_from_words") =
      some ([(ofString "out",.one),(ofString "hi4",.one),(ofString "mid8",.one),(ofString "lo8",.one)],sourceFunctionBody Guest.guestFn_addr_from_words,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "addr_from_words") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "addr_from_words") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "addr_from_words")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 899 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original899 :: declarations.drop 900 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 900)).reverse).all
          (fun entry => !((ofString "addr_from_words") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original899 :: declarations.drop 900) =
          (ofString "addr_from_words",[(ofString "out",ShapeHOL.one),(ofString "hi4",ShapeHOL.one),(ofString "mid8",ShapeHOL.one),(ofString "lo8",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_addr_from_words,ShapeHOL.one) ::
            functionsHOL (declarations.drop 900) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original899_eq]
        simp only [Guest.guestFn_addr_from_words,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "addr_from_words") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "addr_from_words") (functionsHOL (declarations.drop 900)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "addr_from_words") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_addr_from_words

theorem vmBound_addr_from_words : FunBounded (ofString "addr_from_words") 9 :=
  ⟨_,_,_,vmLookup_addr_from_words,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [vmBound_st_be32,vmBound_st_be64]
    · decide⟩

#print axioms vmBound_addr_from_words
end InitECandidate.Runtime
