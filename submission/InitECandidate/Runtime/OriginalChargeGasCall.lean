import InitECandidate.Runtime.ChargeGasCallProgress
import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.CanonicalOriginalSourceFields
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original challenge code installs the authoritative charge_gas body. -/
theorem canonical_original_chargeGas_lookup (input : Guest.InputBlob) :
    (canonicalOriginalSourceEntry input).code.lookup (ofString "charge_gas") =
      some ([(ofString "amount",.one)],sourceFunctionBody Guest.guestFn_charge_gas,.one) := by
  rw [canonical_original_source_code]
  exact originalRuntimeCode_chargeGas_lookup

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
