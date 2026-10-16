import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_refillFrameStateGas_lookup :
    originalRuntimeCode.lookup (ofString "refill_frame_state_gas") =
      some ([],sourceFunctionBody Guest.guestFn_refill_frame_state_gas,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "refill_frame_state_gas") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "refill_frame_state_gas") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "refill_frame_state_gas")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 455 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original455 :: declarations.drop 456 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 456)).reverse).all
          (fun entry => !((ofString "refill_frame_state_gas") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original455 :: declarations.drop 456) =
          (ofString "refill_frame_state_gas",[],sourceFunctionBody Guest.guestFn_refill_frame_state_gas,ShapeHOL.one) ::
            functionsHOL (declarations.drop 456) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original455_eq]
        simp only [Guest.guestFn_refill_frame_state_gas,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "refill_frame_state_gas") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "refill_frame_state_gas") (functionsHOL (declarations.drop 456)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "refill_frame_state_gas") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_refillFrameStateGas_lookup

theorem originalRuntimeCode_frameHalt_lookup :
    originalRuntimeCode.lookup (ofString "frame_halt") =
      some ([(ofString "err",.one)],sourceFunctionBody Guest.guestFn_frame_halt,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "frame_halt") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "frame_halt") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "frame_halt")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 589 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original589 :: declarations.drop 590 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 590)).reverse).all
          (fun entry => !((ofString "frame_halt") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original589 :: declarations.drop 590) =
          (ofString "frame_halt",[(ofString "err",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_frame_halt,ShapeHOL.one) ::
            functionsHOL (declarations.drop 590) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original589_eq]
        simp only [Guest.guestFn_frame_halt,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "frame_halt") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "frame_halt") (functionsHOL (declarations.drop 590)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "frame_halt") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_frameHalt_lookup

end InitECandidate.Runtime
