import InitECandidate.Runtime.ChargeGas
import InitECandidate.Runtime.OriginalRuntimeCode
import InitECandidate.Runtime.PanSingleWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An actual insufficient charge propagates EvmErr 4, spends one call clock,
    and leaves memory untouched. It cannot reach either gas-counter store. -/
theorem evaluate_chargeGas_outOfGas_call (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (argument : ExpHOL 64) (frame left amount : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
        some [.val (.word amount)])
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (frameGlobal : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (exceptionShape : state.eshapes.lookup (ofString "EvmErr") = some .one)
    (leftDomain : state.memaddrs (frame + 64))
    (leftMemory : state.memory (frame + 64) = .word left)
    (insufficient : left.toNat < amount.toNat) :
    evaluateHOLFiniteState state (.call (some (none,none)) (ofString "charge_gas") [argument]) =
      (some (.exception (ofString "EvmErr") (.val (.word 4))),
        emptyLocalsHOLFinite {state with clock := state.clock - 1}) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    HolFiniteMapExact.empty.update (ofString "amount",.val (.word amount))
  let entry := callEntryStateHOLFinite state callee
  have amountLocal : entry.locals.lookup (ofString "amount") = some (.val (.word amount)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have body := evaluate_source_chargeGas_outOfGas entry frame left amount frameGlobal amountLocal
    exceptionShape leftDomain leftMemory insufficient
  have installed : state.code.lookup (ofString "charge_gas") =
      some ([(ofString "amount",.one)],sourceFunctionBody Guest.guestFn_charge_gas,.one) := by
    rw [code]; exact originalRuntimeCode_chargeGas_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "charge_gas") (ofString "amount")
    (sourceFunctionBody Guest.guestFn_charge_gas) amount installed
  have call := evaluateHOLFiniteState_call_exception_no_handler state none (ofString "charge_gas")
    [argument] [.val (.word amount)] (sourceFunctionBody Guest.guestFn_charge_gas) callee .one
    (ofString "EvmErr") (.val (.word 4)) (chargeGasFailurePost entry left) arguments lookup clock body
  exact call

#print axioms evaluate_chargeGas_outOfGas_call
end InitECandidate.Runtime
