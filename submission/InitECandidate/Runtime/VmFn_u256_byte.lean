import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.VmFn_u256_limb

import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 8000000
theorem vmLookup_u256_byte :
    originalRuntimeCode.lookup (ofString "u256_byte") =
      some ([(ofString "i",.one),(ofString "x",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_u256_byte,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "u256_byte") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "u256_byte") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "u256_byte")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 86 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original86 :: declarations.drop 87 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 87)).reverse).all
          (fun entry => !((ofString "u256_byte") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original86 :: declarations.drop 87) =
          (ofString "u256_byte",[(ofString "i",ShapeHOL.one),(ofString "x",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_u256_byte,ShapeHOL.one) ::
            functionsHOL (declarations.drop 87) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original86_eq]
        simp only [Guest.guestFn_u256_byte,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "u256_byte") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "u256_byte") (functionsHOL (declarations.drop 87)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "u256_byte") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_u256_byte

theorem vmBound_u256_byte : FunBounded (ofString "u256_byte") 1 :=
  ⟨_,_,_,vmLookup_u256_byte,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [vmBound_u256_limb]
    · decide⟩

#print axioms vmBound_u256_byte
end InitECandidate.Runtime
