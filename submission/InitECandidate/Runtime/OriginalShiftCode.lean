import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.ShiftOpcodeSource
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_opShl_lookup :
    originalRuntimeCode.lookup (ofString "op_shl") =
      some ([],sourceFunctionBody Guest.guestFn_op_shl,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "op_shl") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "op_shl") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "op_shl")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 500 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original500 :: declarations.drop 501 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 501)).reverse).all
          (fun entry => !((ofString "op_shl") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original500 :: declarations.drop 501) =
          (ofString "op_shl",[],sourceFunctionBody Guest.guestFn_op_shl,ShapeHOL.one) ::
            functionsHOL (declarations.drop 501) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original500_eq]
        simp only [Guest.guestFn_op_shl,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "op_shl") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "op_shl") (functionsHOL (declarations.drop 501)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "op_shl") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]
#print axioms originalRuntimeCode_opShl_lookup

theorem originalRuntimeCode_opShr_lookup :
    originalRuntimeCode.lookup (ofString "op_shr") =
      some ([],sourceFunctionBody Guest.guestFn_op_shr,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "op_shr") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "op_shr") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "op_shr")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 501 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original501 :: declarations.drop 502 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 502)).reverse).all
          (fun entry => !((ofString "op_shr") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original501 :: declarations.drop 502) =
          (ofString "op_shr",[],sourceFunctionBody Guest.guestFn_op_shr,ShapeHOL.one) ::
            functionsHOL (declarations.drop 502) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original501_eq]
        simp only [Guest.guestFn_op_shr,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "op_shr") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "op_shr") (functionsHOL (declarations.drop 502)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "op_shr") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]
#print axioms originalRuntimeCode_opShr_lookup

theorem originalRuntimeCode_opSar_lookup :
    originalRuntimeCode.lookup (ofString "op_sar") =
      some ([],sourceFunctionBody Guest.guestFn_op_sar,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "op_sar") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "op_sar") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "op_sar")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 502 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original502 :: declarations.drop 503 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 503)).reverse).all
          (fun entry => !((ofString "op_sar") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original502 :: declarations.drop 503) =
          (ofString "op_sar",[],sourceFunctionBody Guest.guestFn_op_sar,ShapeHOL.one) ::
            functionsHOL (declarations.drop 503) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original502_eq]
        simp only [Guest.guestFn_op_sar,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "op_sar") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "op_sar") (functionsHOL (declarations.drop 503)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "op_sar") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]
#print axioms originalRuntimeCode_opSar_lookup

/-- Installed declaration lookups of the three direct shift opcodes. -/
theorem shift_opcode_original_lookup (kind : ShiftOpcodeKind) :
 originalRuntimeCode.lookup (shiftOpcodeName kind)=some ([],shiftOpcodeBody kind,.one) := by
 cases kind with
 | shl=>exact originalRuntimeCode_opShl_lookup
 | shr=>exact originalRuntimeCode_opShr_lookup
 | sar=>exact originalRuntimeCode_opSar_lookup
#print axioms shift_opcode_original_lookup
end InitECandidate.Runtime
