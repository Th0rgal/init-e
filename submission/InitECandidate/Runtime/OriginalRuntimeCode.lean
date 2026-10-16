import InitECandidate.Runtime.SourceClock
import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.Pancake.Semantics.PanProps
import InitECandidate.Proofs.FrontendStages.SourceAgreement
import InitECandidate.Proofs.CompactComputation
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Immutable function table of the authoritative original challenge source. -/
def originalRuntimeCode : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) :=
  HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)

private theorem lookup_skip_prefix {A B : Type} [BEq A]
    (before suffix : List (A × B)) (key : A)
    (absent : before.all (fun entry => !(key == entry.1)) = true) :
    List.lookup key (before ++ suffix) = List.lookup key suffix := by
  induction before with
  | nil => rfl
  | cons entry before ih =>
    obtain ⟨name,value⟩ := entry
    simp only [List.all_cons,Bool.and_eq_true] at absent
    cases matchName : (key == name) with
    | false =>
      simp only [List.cons_append,List.lookup_cons,matchName]
      exact ih absent.2
    | true => simp [matchName] at absent

theorem originalRuntimeCode_chargeGas_lookup :
    originalRuntimeCode.lookup (ofString "charge_gas") =
      some ([(ofString "amount",.one)],sourceFunctionBody Guest.guestFn_charge_gas,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "charge_gas") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "charge_gas") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "charge_gas")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 451 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original451 :: declarations.drop 452 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 452)).reverse).all
          (fun entry => !((ofString "charge_gas") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original451 :: declarations.drop 452) =
          (ofString "charge_gas",[(ofString "amount",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_charge_gas,ShapeHOL.one) ::
            functionsHOL (declarations.drop 452) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original451_eq]
        simp only [Guest.guestFn_charge_gas,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "charge_gas") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      rw [lookup_skip_prefix _ _ _ absent]
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]


theorem originalRuntimeCode_pcAdd_lookup :
    originalRuntimeCode.lookup (ofString "pc_add") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_pc_add,.one) := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
  calc
    _ = List.lookup (ofString "pc_add") (functionsHOL sourceDeclarations).reverse := by
      rw [HolFiniteMapExact.lookup_updateList]
      change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) (ofString "pc_add") = _
      simpa only [List.reverse_reverse,FLOOKUP] using
        FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse (ofString "pc_add")
    _ = _ := by
      let declarations := InitECandidate.Proofs.FrontendStages.Declarations.originals
      have split : declarations = declarations.take 471 ++
          InitECandidate.Proofs.FrontendStages.Declarations.original471 :: declarations.drop 472 := by kernel_rfl
      have absent : ((functionsHOL (declarations.drop 472)).reverse).all
          (fun entry => !((ofString "pc_add") == entry.1)) = true := by decide_cbv
      have head : functionsHOL
          (InitECandidate.Proofs.FrontendStages.Declarations.original471 :: declarations.drop 472) =
          (ofString "pc_add",[(ofString "n",ShapeHOL.one)],sourceFunctionBody Guest.guestFn_pc_add,ShapeHOL.one) ::
            functionsHOL (declarations.drop 472) := by
        rw [InitECandidate.Proofs.FrontendStages.Declarations.original471_eq]
        simp only [Guest.guestFn_pc_add,declToHOL,functionsHOL,funDeclToHOL,
          List.map_cons,List.map_nil,paramToHOL,shapeToHOL,sourceFunctionBody]
      rw [InitECandidate.Proofs.FrontendStages.Declarations.sourceDeclarations_eq]
      change List.lookup (ofString "pc_add") (functionsHOL declarations).reverse = _
      rw [split,functionsHOL_append,head,List.reverse_append,List.reverse_cons,List.append_assoc]
      rw [lookup_skip_prefix _ _ _ absent]
      simp only [List.singleton_append,List.lookup_cons,beq_self_eq_true]

#print axioms originalRuntimeCode_chargeGas_lookup
#print axioms originalRuntimeCode_pcAdd_lookup
end InitECandidate.Runtime
