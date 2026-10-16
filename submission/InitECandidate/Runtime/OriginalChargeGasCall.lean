import InitECandidate.Runtime.ChargeGasCallProgress
import InitECandidate.Runtime.CanonicalOriginalSourceFields
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

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

/-- The original challenge code installs the authoritative charge_gas body. -/
theorem canonical_original_chargeGas_lookup (input : Guest.InputBlob) :
    (canonicalOriginalSourceEntry input).code.lookup (ofString "charge_gas") =
      some ([(ofString "amount",.one)],sourceFunctionBody Guest.guestFn_charge_gas,.one) := by
  rw [canonical_original_source_code]
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

/-- Positive charge call progress specialized to the actual immutable original
code table, rather than a supplied body/parameter lookup certificate. -/
theorem original_chargeGas_call_positive_progress (input : Guest.InputBlob)
    (state : PanSemStateFiniteExact 64 Guest.HostMemory) (argument : ExpHOL 64)
    (frame amount : BitVec 64) (funding : GasFunding)
    (code : state.code = (canonicalOriginalSourceEntry input).code)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word amount)])
    (clock : state.clock ≠ 0)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (leftDomain : state.memaddrs (frame + 64)) (usedDomain : state.memaddrs (frame + 184))
    (memory : HasGasFunding state frame funding)
    (budget : funding.potential ≤ 200000000) (enough : amount ≤ funding.left)
    (positive : 0 < amount.toNat) :
    ∃ post, evaluateHOLFiniteState state
        (.call (some (none,none)) (ofString "charge_gas") [argument]) = (none,post) ∧
      HasGasFunding post frame (funding.charge amount) ∧
      (funding.charge amount).potential = funding.potential ∧
      post.clock = state.clock - 1 ∧ post.locals = state.locals ∧
      funding.used.toNat + 1 ≤ (funding.charge amount).used.toNat ∧
      (funding.charge amount).used.toNat ≤ 200000000 := by
  have installed : state.code.lookup (ofString "charge_gas") =
      some ([(ofString "amount",.one)],sourceFunctionBody Guest.guestFn_charge_gas,.one) := by
    rw [code]
    exact canonical_original_chargeGas_lookup input
  exact chargeGas_call_positive_progress state argument frame amount funding arguments installed clock
    hFrame leftDomain usedDomain memory budget enough positive

#print axioms canonical_original_chargeGas_lookup
#print axioms original_chargeGas_call_positive_progress
end InitECandidate.Runtime
