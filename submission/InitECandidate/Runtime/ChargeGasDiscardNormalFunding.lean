import InitECandidate.Runtime.ChargeGasReturnedEnough
import InitECandidate.Runtime.InterpreterFundingCharge
import InitECandidate.Runtime.PanDiscardNormalBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Actual successful original charge_gas derives its own fee sufficiency and
one consumed clock before using the concrete physical/global funding theorem. -/
theorem charge_gas_discard_normal_funding
 (s post : PanSemStateFiniteExact 64 Guest.HostMemory)
 (lower upper : Nat) (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s lower upper (current::ancestors))
 (argument : ExpHOL 64) (amount : BitVec 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [argument]=some [.val (.word amount)])
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word current.address)))
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "charge_gas") [argument])=(none,post)) :
 amount≤current.gas.left ∧post=chargeGasCallPost s current.address current.gas amount ∧
 InterpreterFundingLayout post lower upper (current.charged amount::ancestors) ∧
 interpreterFundingUsed (current.charged amount::ancestors)=interpreterFundingUsed (current::ancestors)+amount.toNat ∧
 post.globals=s.globals ∧post.clock=s.clock-1 ∧post.locals=s.locals ∧
 (∀watched : BitVec 64,upper≤watched.toNat→post.memory watched=s.memory watched) := by
 have currentAt:=layout.records current (by simp)
 have installed : s.code.lookup (ofString "charge_gas")=some ([(ofString "amount",.one)],sourceFunctionBody Guest.guestFn_charge_gas,.one) := by
  rw [code];exact originalRuntimeCode_chargeGas_lookup
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=HolFiniteMapExact.empty.update (ofString "amount",.val (.word amount))
 have lookup:=pan_single_word_lookup s.code.lookup (ofString "charge_gas") (ofString "amount") (sourceFunctionBody Guest.guestFn_charge_gas) amount installed
 have ticks : s.clock≠0 := by
  intro zero
  rw [evaluateHOLFiniteState_call,args] at run
  simp only at run
  rw [lookup] at run
  simp [zero] at run
 obtain ⟨value,bodyPost,bodyRun,_,_⟩:=evaluate_discard_normal_body s post (ofString "charge_gas") [argument] _ _ callee .one args lookup run
 have atAmount : (callEntryStateHOLFinite s callee).locals.lookup (ofString "amount")=some (.val (.word amount)) := by
  simp [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have enough:=charge_gas_returned_enough (callEntryStateHOLFinite s callee) bodyPost current.address current.gas.left amount value atFrame atAmount
  (currentAt.readable 64 (by simp [interpreterFundingOffsets])) currentAt.funding.1 bodyRun
 have exactCall:=evaluate_chargeGas_call s argument current.address amount current.gas args installed ticks atFrame
  (currentAt.readable 64 (by simp [interpreterFundingOffsets])) (currentAt.readable 184 (by simp [interpreterFundingOffsets])) currentAt.funding enough
 have postEq : post=chargeGasCallPost s current.address current.gas amount:=(Prod.mk.inj (run.symm.trans exactCall)).2
 obtain ⟨samePost,sameRun,funding,used,globals,clock,memory⟩:=interpreter_funding_charge_call s lower upper current ancestors layout amount argument code atFrame args enough ticks
 have same : samePost=post:=(Prod.mk.inj (sameRun.symm.trans run)).2
 subst samePost
 exact ⟨enough,postEq,funding,used,globals,clock,by rw [postEq];rfl,memory⟩
#print axioms charge_gas_discard_normal_funding
end InitECandidate.Runtime
