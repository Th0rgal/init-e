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
theorem vmLookup_ec_set_affine :
    originalRuntimeCode.lookup (ofString "ec_set_affine") =
      some ([(ofString "pt",.one),(ofString "x",.comb [.one,.one,.one,.one]),(ofString "y",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_ec_set_affine,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "ec_set_affine") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "ec_set_affine") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "ec_set_affine")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 174 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original174 :: declarations.drop 175 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 175)).reverse).all
          (fun entry => !((ofString "ec_set_affine") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original174 :: declarations.drop 175) =
          (ofString "ec_set_affine",[(ofString "pt",ShapeHOL.one),(ofString "x",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one]),(ofString "y",ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one,ShapeHOL.one,ShapeHOL.one])],sourceFunctionBody Guest.guestFn_ec_set_affine,ShapeHOL.one) ::
            functionsHOL (declarations.drop 175) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original174_eq]
        simp only [Guest.guestFn_ec_set_affine,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "ec_set_affine") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "ec_set_affine") (functionsHOL (declarations.drop 175)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "ec_set_affine") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms vmLookup_ec_set_affine

theorem vmBound_ec_set_affine : FunBounded (ofString "ec_set_affine") 0 :=
  ⟨_,_,_,vmLookup_ec_set_affine,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound []
    · decide⟩

#print axioms vmBound_ec_set_affine
end InitECandidate.Runtime
