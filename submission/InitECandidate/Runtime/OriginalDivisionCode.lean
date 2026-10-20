import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.DivisionOpcodeSource
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_opDiv_lookup :
    originalRuntimeCode.lookup (ofString "op_div") =
      some ([],sourceFunctionBody Guest.guestFn_op_div,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "op_div") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "op_div") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "op_div")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 481 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original481 :: declarations.drop 482 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 482)).reverse).all
          (fun entry => !((ofString "op_div") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original481 :: declarations.drop 482) =
          (ofString "op_div",[],sourceFunctionBody Guest.guestFn_op_div,ShapeHOL.one) ::
            functionsHOL (declarations.drop 482) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original481_eq]
        simp only [Guest.guestFn_op_div,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "op_div") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "op_div") (functionsHOL (declarations.drop 482)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "op_div") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]
#print axioms originalRuntimeCode_opDiv_lookup

theorem originalRuntimeCode_opSdiv_lookup :
    originalRuntimeCode.lookup (ofString "op_sdiv") =
      some ([],sourceFunctionBody Guest.guestFn_op_sdiv,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "op_sdiv") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "op_sdiv") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "op_sdiv")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 482 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original482 :: declarations.drop 483 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 483)).reverse).all
          (fun entry => !((ofString "op_sdiv") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original482 :: declarations.drop 483) =
          (ofString "op_sdiv",[],sourceFunctionBody Guest.guestFn_op_sdiv,ShapeHOL.one) ::
            functionsHOL (declarations.drop 483) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original482_eq]
        simp only [Guest.guestFn_op_sdiv,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "op_sdiv") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "op_sdiv") (functionsHOL (declarations.drop 483)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "op_sdiv") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]
#print axioms originalRuntimeCode_opSdiv_lookup

theorem originalRuntimeCode_opMod_lookup :
    originalRuntimeCode.lookup (ofString "op_mod") =
      some ([],sourceFunctionBody Guest.guestFn_op_mod,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "op_mod") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "op_mod") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "op_mod")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 483 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original483 :: declarations.drop 484 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 484)).reverse).all
          (fun entry => !((ofString "op_mod") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original483 :: declarations.drop 484) =
          (ofString "op_mod",[],sourceFunctionBody Guest.guestFn_op_mod,ShapeHOL.one) ::
            functionsHOL (declarations.drop 484) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original483_eq]
        simp only [Guest.guestFn_op_mod,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "op_mod") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "op_mod") (functionsHOL (declarations.drop 484)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "op_mod") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]
#print axioms originalRuntimeCode_opMod_lookup

theorem originalRuntimeCode_opSmod_lookup :
    originalRuntimeCode.lookup (ofString "op_smod") =
      some ([],sourceFunctionBody Guest.guestFn_op_smod,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "op_smod") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "op_smod") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "op_smod")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 484 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original484 :: declarations.drop 485 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 485)).reverse).all
          (fun entry => !((ofString "op_smod") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original484 :: declarations.drop 485) =
          (ofString "op_smod",[],sourceFunctionBody Guest.guestFn_op_smod,ShapeHOL.one) ::
            functionsHOL (declarations.drop 485) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original484_eq]
        simp only [Guest.guestFn_op_smod,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "op_smod") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "op_smod") (functionsHOL (declarations.drop 485)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "op_smod") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]
#print axioms originalRuntimeCode_opSmod_lookup

/-- Installed declaration lookups of the four division opcodes. -/
theorem division_opcode_original_lookup (kind : DivisionOpcodeKind) :
 originalRuntimeCode.lookup (divisionOpcodeName kind)=some ([],divisionOpcodeBody kind,.one) := by
 cases kind with
 | div=>exact originalRuntimeCode_opDiv_lookup
 | sdiv=>exact originalRuntimeCode_opSdiv_lookup
 | mod=>exact originalRuntimeCode_opMod_lookup
 | smod=>exact originalRuntimeCode_opSmod_lookup
#print axioms division_opcode_original_lookup
end InitECandidate.Runtime
