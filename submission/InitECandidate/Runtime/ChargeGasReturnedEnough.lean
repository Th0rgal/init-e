import InitECandidate.Runtime.ChargeGas
import InitECandidate.Runtime.FundingAllocationReturnedContext
import InitECandidate.Runtime.TrapNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- An actual successful charge_gas body passed its real unsigned gas guard.
No available-gas or exception-shape premise is assumed. -/
theorem charge_gas_returned_enough
 (s post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame left amount : BitVec 64)
 (value : ValueHOL 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (atAmount : s.locals.lookup (ofString "amount")=some (.val (.word amount)))
 (domain : s.memaddrs (frame+64)) (leftAt : s.memory (frame+64)=.word left)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_charge_gas)=(some (.returned value),post)) :
 amount≤left := by
 rw [source_chargeGas_body] at run
 obtain ⟨loaded,output,loadedEval,tailRun,scope⟩:=funding_declaration_returned_context run
 have exactLoad:=eval_fundingLoad s frame 64 left atFrame domain leftAt
 have loadedEq : loaded=.val (.word left):=Option.some.inj (loadedEval.symm.trans exactLoad)
 subst loaded
 let entry:=setVarHOLFinite (ofString "gl") (.val (.word left)) s
 change evaluateHOLFiniteState entry chargeGasTail=_ at tailRun
 have atLeft : entry.locals.lookup (ofString "gl")=some (.val (.word left)) := by
  simp [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have amountAt : entry.locals.lookup (ofString "amount")=some (.val (.word amount)) := by
  simpa (config:={decide:=true}) [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atAmount
 apply BitVec.le_def.mpr
 by_contra insufficient
 have larger : left.toNat<amount.toNat := by omega
 rw [chargeGasTail,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,
  eval_chargeGasCheck entry left amount atLeft amountAt] at tailRun
 simp only [if_pos larger] at tailRun
 have noNormal : (evaluateHOLFiniteState entry (.raise (ofString "EvmErr") (.const 4))).1≠none := by
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only;split <;>simp
  · simp
 have noReturn:=evaluate_raise_no_return entry (ofString "EvmErr") (.const 4) value
 cases raised : evaluateHOLFiniteState entry (.raise (ofString "EvmErr") (.const 4)) with
 | mk result next =>
  rw [raised] at tailRun noNormal noReturn
  cases result with
  | none=>exact noNormal rfl
  | some r=>exact noReturn (Prod.mk.inj tailRun).1
#print axioms charge_gas_returned_enough
end InitECandidate.Runtime
