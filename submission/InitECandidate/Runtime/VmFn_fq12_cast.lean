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
theorem vmLookup_fq12_cast :
    originalRuntimeCode.lookup (ofString "fq12_cast") =
      some ([(ofString "out",.one),(ofString "g1",.one)],sourceFunctionBody Guest.guestFn_fq12_cast,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "fq12_cast") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "fq12_cast") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "fq12_cast")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 703 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original703 :: declarations.drop 704 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 704)).reverse).all
          (fun entry => !((ofString "fq12_cast") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original703 :: declarations.drop 704) =
          (ofString "fq12_cast",[(ofString "out",ShapeHOL.one),(ofString "g1",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_fq12_cast,ShapeHOL.one) ::
            functionsHOL (declarations.drop 704) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original703_eq]
        simp only [Guest.guestFn_fq12_cast,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "fq12_cast") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "fq12_cast") (functionsHOL (declarations.drop 704)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "fq12_cast") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_fq12_cast

theorem vmBound_fq12_cast : FunBounded (ofString "fq12_cast") 191 :=
  ⟨_,_,_,vmLookup_fq12_cast,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound []
    · decide⟩

#print axioms vmBound_fq12_cast
end InitECandidate.Runtime
