import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_opJumpdest_lookup :
    originalRuntimeCode.lookup (ofString "op_jumpdest") =
      some ([],sourceFunctionBody Guest.guestFn_op_jumpdest,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "op_jumpdest") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "op_jumpdest") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "op_jumpdest")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 510 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original510 :: declarations.drop 511 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 511)).reverse).all
          (fun entry => !((ofString "op_jumpdest") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original510 :: declarations.drop 511) =
          (ofString "op_jumpdest",[],sourceFunctionBody Guest.guestFn_op_jumpdest,ShapeHOL.one) ::
            functionsHOL (declarations.drop 511) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original510_eq]
        simp only [Guest.guestFn_op_jumpdest,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "op_jumpdest") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "op_jumpdest") (functionsHOL (declarations.drop 511)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "op_jumpdest") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_opJumpdest_lookup

theorem originalRuntimeCode_opStop_lookup :
    originalRuntimeCode.lookup (ofString "op_stop") =
      some ([],sourceFunctionBody Guest.guestFn_op_stop,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "op_stop") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "op_stop") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "op_stop")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 505 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original505 :: declarations.drop 506 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 506)).reverse).all
          (fun entry => !((ofString "op_stop") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original505 :: declarations.drop 506) =
          (ofString "op_stop",[],sourceFunctionBody Guest.guestFn_op_stop,ShapeHOL.one) ::
            functionsHOL (declarations.drop 506) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original505_eq]
        simp only [Guest.guestFn_op_stop,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "op_stop") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "op_stop") (functionsHOL (declarations.drop 506)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "op_stop") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_opStop_lookup
end InitECandidate.Runtime
