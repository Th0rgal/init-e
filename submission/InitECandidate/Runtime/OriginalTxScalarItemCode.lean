import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_txScalarItem_lookup :
    originalRuntimeCode.lookup (ofString "tx_scalar_item") =
      some ([(ofString "arr",.one),(ofString "i",.one),(ofString "maxb",.one)],sourceFunctionBody Guest.guestFn_tx_scalar_item,.comb [.one,.one]) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "tx_scalar_item") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "tx_scalar_item") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "tx_scalar_item")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 299 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original299 :: declarations.drop 300 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 300)).reverse).all
          (fun entry => !((ofString "tx_scalar_item") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original299 :: declarations.drop 300) =
          (ofString "tx_scalar_item",[(ofString "arr",ShapeHOL.one),(ofString "i",ShapeHOL.one),(ofString "maxb",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_tx_scalar_item,ShapeHOL.comb [ShapeHOL.one,ShapeHOL.one]) ::
            functionsHOL (declarations.drop 300) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original299_eq]
        simp only [Guest.guestFn_tx_scalar_item,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "tx_scalar_item") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "tx_scalar_item") (functionsHOL (declarations.drop 300)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "tx_scalar_item") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_txScalarItem_lookup

end InitECandidate.Runtime
