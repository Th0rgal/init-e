import InitECandidate.Runtime.MessageCallGasReturnedStipend
import InitECandidate.Runtime.AddSat
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def sourceCallStipend (zeroFlag : BitVec 64) : BitVec 64:=if zeroFlag=0 then 2300 else 0
def sourceCallAccessTransferFee (warm zeroFlag : BitVec 64) : BitVec 64:=
 (if warm=0 then 3000 else 100)+(if zeroFlag=0 then 11300 else 0)

/-- The actual source's access/transfer literals pay the stipend plus positive
regular progress, even with arbitrary saturating memory-cost additions. -/
theorem source_call_fee_pays_stipend (warm zeroFlag memoryCost : BitVec 64) :
 (sourceCallStipend zeroFlag).toNat+1≤(wordAddSat (sourceCallAccessTransferFee warm zeroFlag) memoryCost).toNat := by
 rw [wordAddSat_toNat]
 by_cases cold : warm=0 <;>by_cases value : zeroFlag=0
 all_goals first | change warm=0#64 at cold | change warm≠0#64 at cold
 all_goals first | change zeroFlag=0#64 at value | change zeroFlag≠0#64 at value
 all_goals simp [sourceCallAccessTransferFee,sourceCallStipend,cold,value]
 all_goals omega

/-- Combining the real calculator with prior source fee payment conserves
pending child funding and leaves a strict net-used increment. Fee provenance
is explicit until the actual opcode prefix establishes the fee literal case. -/
theorem message_call_actual_funded_delegation {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (parent : GasFunding) (fee requested a b c d : BitVec 64) (value : ValueHOL 64)
 (atValue : s.locals.lookup (ofString "value")=some (fundingU256 a b c d))
 (atRequested : s.locals.lookup (ofString "gas")=some (.val (.word requested)))
 (atRemaining : s.locals.lookup (ofString "gas_left")=some (.val (.word (parent.charge fee).left)))
 (atMemory : s.locals.lookup (ofString "memory_cost")=some (.val (.word (0#64))))
 (atExtra : s.locals.lookup (ofString "extra_gas")=some (.val (.word (0#64))))
 (code : s.code=originalRuntimeCode) (budget : parent.potential≤200000000)
 (feeEnough : fee≤parent.left)
 (feePays : (sourceCallStipend (fundingU256ZeroFlag a b c d)).toNat+1≤fee.toNat)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_calculate_message_call_gas)=(some (.returned value),post)) :
 ∃forwarded allocated : BitVec 64,value=.rStruct [.val (.word forwarded),.val (.word allocated)] ∧
 forwarded≤(parent.charge fee).left ∧allocated.toNat≤(parent.charge fee).used.toNat+forwarded.toNat ∧
 ((parent.charge fee).delegate forwarded allocated).potential+(childFunding allocated).potential=parent.potential ∧
 parent.used.toNat+1≤((parent.charge fee).delegate forwarded allocated).used.toNat := by
 have chargedBudget : (parent.charge fee).potential≤200000000 := by rw [parent.charge_potential fee budget feeEnough];exact budget
 have remainingBound : (parent.charge fee).left.toNat≤200000000:=by have:=chargedBudget;unfold GasFunding.potential at this;omega
 obtain ⟨forwarded,allocated,stipend,returned,below,stipendEq,stipendBound,allocationEq⟩:=message_call_gas_actual_returned_stipend s post requested (parent.charge fee).left a b c d value atValue atRequested atRemaining atMemory atExtra code remainingBound run
 have pays : stipend.toNat+1≤fee.toNat:=by simpa [stipendEq,sourceCallStipend] using feePays
 have progress:=call_delegation_progress parent fee forwarded allocated stipend.toNat budget feeEnough below allocationEq pays
 have usedGrowth : (parent.charge fee).used.toNat=parent.used.toNat+fee.toNat := by
  have total : parent.left.toNat+parent.used.toNat≤200000000:=by unfold GasFunding.potential at budget;omega
  exact parent.charge_used_growth fee budget feeEnough
 have allocationEnough : allocated.toNat≤(parent.charge fee).used.toNat+forwarded.toNat := by rw [usedGrowth,allocationEq];omega
 have conserved:=(parent.charge fee).delegate_potential forwarded allocated chargedBudget below allocationEnough
 rw [parent.charge_potential fee budget feeEnough] at conserved
 exact ⟨forwarded,allocated,returned,below,allocationEnough,conserved,progress⟩
#print axioms source_call_fee_pays_stipend
#print axioms message_call_actual_funded_delegation
end InitECandidate.Runtime
