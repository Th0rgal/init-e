import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.VmFn_max
import InitECandidate.Runtime.VmFn_u256_bit_length

import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 8000000
theorem vmLookup_modexp_gas :
    originalRuntimeCode.lookup (ofString "modexp_gas") =
      some ([(ofString "blen",.one),(ofString "mlen",.one),(ofString "elen",.one),(ofString "head",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_modexp_gas,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "modexp_gas") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "modexp_gas") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "modexp_gas")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 867 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original867 :: declarations.drop 868 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 868)).reverse).all
          (fun entry => !((ofString "modexp_gas") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original867 :: declarations.drop 868) =
          (ofString "modexp_gas",[(ofString "blen",ShapeHOL.one),(ofString "mlen",ShapeHOL.one),(ofString "elen",ShapeHOL.one),(ofString "head",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_modexp_gas,ShapeHOL.one) ::
            functionsHOL (declarations.drop 868) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original867_eq]
        simp only [Guest.guestFn_modexp_gas,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "modexp_gas") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "modexp_gas") (functionsHOL (declarations.drop 868)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "modexp_gas") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_modexp_gas

theorem vmBound_modexp_gas : FunBounded (ofString "modexp_gas") 6 :=
  ⟨_,_,_,vmLookup_modexp_gas,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [vmBound_max,vmBound_u256_bit_length]
    · decide⟩

#print axioms vmBound_modexp_gas
end InitECandidate.Runtime
