import InitECandidate.Runtime.ChargeGasCallProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

noncomputable def chargeGasCallPost (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame : BitVec 64) (funding : GasFunding) (amount : BitVec 64) :=
  sourceWriteWord (sourceWriteWord {state with clock := state.clock - 1}
    (frame + 64) (funding.left - amount)) (frame + 184) (funding.used + amount)

/-- Exact footprint of an actual successful charge_gas call. -/
theorem evaluate_chargeGas_call (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (argument : ExpHOL 64) (frame amount : BitVec 64) (funding : GasFunding)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word amount)])
    (installed : state.code.lookup (ofString "charge_gas") =
      some ([(ofString "amount",.one)],sourceFunctionBody Guest.guestFn_charge_gas,.one))
    (clock : state.clock ≠ 0)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (leftDomain : state.memaddrs (frame + 64)) (usedDomain : state.memaddrs (frame + 184))
    (memory : HasGasFunding state frame funding) (enough : amount ≤ funding.left) :
    evaluateHOLFiniteState state (.call (some (none,none)) (ofString "charge_gas") [argument]) =
      (none,chargeGasCallPost state frame funding amount) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    HolFiniteMapExact.empty.update (ofString "amount",.val (.word amount))
  let entry := callEntryStateHOLFinite state callee
  have argumentLocal : entry.locals.lookup (ofString "amount") = some (.val (.word amount)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have body := evaluate_source_chargeGas entry frame funding.left funding.used amount hFrame argumentLocal
    leftDomain usedDomain memory.1 memory.2.1 enough
  have lookup := pan_single_word_lookup state.code.lookup (ofString "charge_gas") (ofString "amount")
    (sourceFunctionBody Guest.guestFn_charge_gas) amount installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "charge_gas")
    [argument] [.val (.word amount)] (sourceFunctionBody Guest.guestFn_charge_gas) callee .one
    (.val (.word 0)) (chargeGasPost entry frame funding.left funding.used amount) arguments lookup clock body
    (by simp [shapeOfHOLExact,shapeEqHOL])
  exact call

theorem chargeGasCallPost_funding (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame amount : BitVec 64) (funding : GasFunding) (memory : HasGasFunding state frame funding) :
    HasGasFunding (chargeGasCallPost state frame funding amount) frame (funding.charge amount) := by
  simp [HasGasFunding,chargeGasCallPost,sourceWriteWord,GasFunding.charge]
  exact memory.2.2

theorem chargeGasCallPost_pc (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame pc amount : BitVec 64) (funding : GasFunding) (memory : state.memory (frame + 0) = .word pc) :
    (chargeGasCallPost state frame funding amount).memory (frame + 0) = .word pc := by
  simpa [chargeGasCallPost,sourceWriteWord] using memory

#print axioms evaluate_chargeGas_call
#print axioms chargeGasCallPost_funding
#print axioms chargeGasCallPost_pc
end InitECandidate.Runtime
