import InitECandidate.Runtime.ChargeGasProgress
import InitECandidate.Runtime.PanSingleWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual opcode-style charge_gas call consumes exactly one source clock,
restores caller locals, and makes positive progress in the bounded used counter. -/
theorem chargeGas_call_positive_progress (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (argument : ExpHOL 64) (frame amount : BitVec 64) (funding : GasFunding)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word amount)])
    (installed : state.code.lookup (ofString "charge_gas") =
      some ([(ofString "amount",.one)],sourceFunctionBody Guest.guestFn_charge_gas,.one))
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
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    HolFiniteMapExact.empty.update (ofString "amount",.val (.word amount))
  let entry := callEntryStateHOLFinite state callee
  have amountLocal : entry.locals.lookup (ofString "amount") = some (.val (.word amount)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨bodyPost,bodyRun,related,potential,bodyClock,progress,bound⟩ :=
    chargeGas_positive_progress entry frame amount funding hFrame amountLocal leftDomain usedDomain memory budget enough positive
  have lookup := pan_single_word_lookup state.code.lookup (ofString "charge_gas") (ofString "amount")
    (sourceFunctionBody Guest.guestFn_charge_gas) amount installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "charge_gas")
    [argument] [.val (.word amount)] (sourceFunctionBody Guest.guestFn_charge_gas) callee .one
    (.val (.word 0)) bodyPost arguments lookup clock bodyRun (by simp [shapeOfHOLExact,shapeEqHOL])
  exact ⟨{bodyPost with locals := state.locals},call,related,potential,bodyClock,rfl,progress,bound⟩

#print axioms chargeGas_call_positive_progress
end InitECandidate.Runtime
