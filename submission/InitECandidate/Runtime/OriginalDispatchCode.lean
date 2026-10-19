import InitECandidate.Runtime.OriginalRuntimeCode
import Init.Data.List.Find
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem originalRuntimeCode_acctIsEmpty_lookup :
    originalRuntimeCode.lookup (ofString "acct_is_empty") =
      some ([(ofString "a",.one)],sourceFunctionBody Guest.guestFn_acct_is_empty,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "acct_is_empty") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "acct_is_empty") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "acct_is_empty")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 387 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original387 :: declarations.drop 388 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 388)).reverse).all
          (fun entry => !((ofString "acct_is_empty") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original387 :: declarations.drop 388) =
          (ofString "acct_is_empty",[(ofString "a",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_acct_is_empty,ShapeHOL.one) ::
            functionsHOL (declarations.drop 388) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original387_eq]
        simp only [Guest.guestFn_acct_is_empty,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "acct_is_empty") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "acct_is_empty") (functionsHOL (declarations.drop 388)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "acct_is_empty") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

theorem originalRuntimeCode_chargeStateGas_lookup :
    originalRuntimeCode.lookup (ofString "charge_state_gas") =
      some ([(ofString "amount",.one)],sourceFunctionBody Guest.guestFn_charge_state_gas,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "charge_state_gas") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "charge_state_gas") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "charge_state_gas")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 452 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original452 :: declarations.drop 453 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 453)).reverse).all
          (fun entry => !((ofString "charge_state_gas") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original452 :: declarations.drop 453) =
          (ofString "charge_state_gas",[(ofString "amount",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_charge_state_gas,ShapeHOL.one) ::
            functionsHOL (declarations.drop 453) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original452_eq]
        simp only [Guest.guestFn_charge_state_gas,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "charge_state_gas") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "charge_state_gas") (functionsHOL (declarations.drop 453)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "charge_state_gas") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

theorem originalRuntimeCode_prepareDispatch_lookup :
    originalRuntimeCode.lookup (ofString "prepare_dispatch") =
      some ([],sourceFunctionBody Guest.guestFn_prepare_dispatch,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "prepare_dispatch") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "prepare_dispatch") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "prepare_dispatch")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 579 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original579 :: declarations.drop 580 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 580)).reverse).all
          (fun entry => !((ofString "prepare_dispatch") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original579 :: declarations.drop 580) =
          (ofString "prepare_dispatch",[],sourceFunctionBody Guest.guestFn_prepare_dispatch,ShapeHOL.one) ::
            functionsHOL (declarations.drop 580) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original579_eq]
        simp only [Guest.guestFn_prepare_dispatch,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "prepare_dispatch") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      have noLookup : List.lookup (ofString "prepare_dispatch") (functionsHOL (declarations.drop 580)).reverse = none := by
        apply List.lookup_eq_none_iff.mpr
        simpa only [bne] using List.all_eq_true.mp absent
      rw [List.lookup_append,noLookup]
      change List.lookup (ofString "prepare_dispatch") (_ ++ _) = _
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_acctIsEmpty_lookup
#print axioms originalRuntimeCode_chargeStateGas_lookup
#print axioms originalRuntimeCode_prepareDispatch_lookup

end InitECandidate.Runtime
