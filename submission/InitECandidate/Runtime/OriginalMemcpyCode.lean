import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_memcpy_lookup :
    originalRuntimeCode.lookup (ofString "memcpy") =
      some ([(ofString "dst",.one),(ofString "src",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_memcpy,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "memcpy") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "memcpy") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "memcpy")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 17 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original17 :: declarations.drop 18 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 18)).reverse).all
          (fun entry => !((ofString "memcpy") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original17 :: declarations.drop 18) =
          (ofString "memcpy",[(ofString "dst",ShapeHOL.one),(ofString "src",ShapeHOL.one),(ofString "n",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_memcpy,ShapeHOL.one) ::
            functionsHOL (declarations.drop 18) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original17_eq]
        simp only [Guest.guestFn_memcpy,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "memcpy") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "memcpy") (functionsHOL (declarations.drop 18)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "memcpy") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_memcpy_lookup

end InitECandidate.Runtime
