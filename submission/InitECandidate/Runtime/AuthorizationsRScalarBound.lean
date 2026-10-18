import InitECandidate.Runtime.FourWordValueShape
import InitECandidate.Runtime.TxScalarU256InputPrefix
import InitECandidate.Runtime.TxScalarU256InputGlobals
import InitECandidate.Runtime.AuthorizationsRStoreLastBound
import InitECandidate.Runtime.PanDecCallCheckedContinuationBound
import InitECandidate.Runtime.AuthorizationsRTailSource
import InitECandidate.Runtime.FourWordStoreInputPrefix
import InitECandidate.Runtime.AuthorizationsLastScalarBound
import InitECandidate.Runtime.NamedGlobalFrame
import InitECandidate.Runtime.AuthorizationsTailSource
import InitECandidate.Runtime.TxScalarU256DeclarationInputBound
import InitECandidate.Runtime.TxScalarU256InputBound
import InitECandidate.Runtime.OriginalTxScalarU256Code
import InitECandidate.Runtime.PanThreeWordShapeLookup
import InitECandidate.Runtime.PanDecCallStraightBound
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem authorization_two_call_entry_budget (work before : Nat)
    (budget : 2 * (work + 92668) ≤ before) : work + 92667 ≤ before - 1 := by omega

theorem authorization_two_call_tail_budget (work before after : Nat)
    (budget : 2 * (work + 92668) ≤ before) (spent : before - 1 ≤ after + (work + 92667)) :
    work + 92668 ≤ after := by omega

/-- The actual final two u256 authorization fields, their stores and index
increment share a finite polynomial bound in the original input length. -/
theorem evaluate_authorization_r_scalar_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (record array count input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atRecord : state.locals.lookup (ofString "a") = some (.val (.word record)))
    (before : array.toNat + count.toNat * 16 ≤ record.toNat ∨ record.toNat + 120 ≤ array.toNat) (fits : record.toNat + 120 < 2^64)
    (entryLocal : state.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : 5 < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (arrayBelowFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (budget : 2 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state authorizationRScalar
    state.clock ≤ evaluated.2.clock + 2 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let cost := inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668
  let callee := txScalarWordCallee array 4 32
  let entry := callEntryStateHOLFinite state callee
  have atArray : entry.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp [entry,callee,callEntryStateHOLFinite,txScalarWordCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "maxb" ≠ ofString "arr" by decide,show ofString "i" ≠ ofString "arr" by decide]
  have atIndex : entry.locals.lookup (ofString "i") = some (.val (.word (4 : BitVec 64))) := by
    simp [entry,callee,callEntryStateHOLFinite,txScalarWordCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "maxb" ≠ ofString "i" by decide]
  have atMaximum : entry.locals.lookup (ofString "maxb") = some (.val (.word (32 : BitVec 64))) := by
    simp [entry,callee,callEntryStateHOLFinite,txScalarWordCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryPrefix : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := valid slot inside
    exact ⟨p,n,item.after_frame state entry array slot p n input inputLength rfl rfl rfl⟩
  have inside4 : (4 : BitVec 64).toNat < count.toNat := by change 4 < count.toNat; omega
  have bodyBudget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92667 ≤ entry.clock := by
    change inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92667 ≤ state.clock - 1
    exact authorization_two_call_entry_budget _ _ budget
  have bounded := evaluate_txScalarU256_input_bounded entry array 4 32 input inputLength scratch frame count.toNat ceiling inputLimit
    atArray atIndex atMaximum entryPrefix inside4 inputBound limitBound scratchGlobal frameGlobal code orderedFrame
    framePositive scratchBelow arena bodyBudget
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.rfield 0 (.var .local (ofString "ent")),.const 4,.const 32] =
      some [.val (.word array),.val (.word (4 : BitVec 64)),.val (.word (32 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,entryLocal]
  have installed := originalRuntimeCode_txScalarU256_lookup
  rw [← code] at installed
  have lookup := pan_three_word_shape_lookup state.code.lookup (ofString "tx_scalar_u256")
    (ofString "arr") (ofString "i") (ofString "maxb") (sourceFunctionBody Guest.guestFn_tx_scalar_u256)
    (.comb [.one,.one,.one,.one]) array 4 32 (by decide) (by decide) (by decide) installed
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_tx_scalar_u256) with
  | mk result post =>
    rw [bodyRun] at bounded
    dsimp only at bounded
    have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_tx_scalar_u256)
    rw [bodyRun] at metadata
    dsimp only at metadata
    have bodyCost : state.clock - 1 ≤ post.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92667) := bounded.1
    have positive : 0 < state.clock := by omega
    have callCost : state.clock ≤ post.clock + cost := by dsimp only [cost]; omega
    have tailBudget : cost ≤ post.clock := authorization_two_call_tail_budget _ _ _ budget bodyCost
    rw [source_authorization_r_scalar]
    have composed := evaluate_decCall_checked_continuation_bounded state post (ofString "r") (ofString "tx_scalar_u256")
      (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one])
      [.rfield 0 (.var .local (ofString "ent")),.const 4,.const 32]
      [.val (.word array),.val (.word (4 : BitVec 64)),.val (.word (32 : BitVec 64))]
      (sourceFunctionBody Guest.guestFn_tx_scalar_u256) authorizationRStoreAndLast callee result cost cost
      args lookup (Nat.ne_of_gt positive) bodyRun bounded.2.1 callCost bounded.2.2 ?_
    · simpa only [cost,two_mul] using composed
    · intro value returned checked
      have retained := txScalarU256_input_returned_prefix entry post array 4 32 input inputLength scratch frame count ceiling inputLimit
        atArray atIndex atMaximum entryPrefix inside4 inputBound limitBound scratchGlobal frameGlobal code orderedFrame
        framePositive scratchBelow arena bodyBudget arrayBelowFrame value (by rw [bodyRun]; exact congrArg (fun r => (r,post)) returned)
      have globals := txScalarU256_input_returned_globals entry post array 4 32 input inputLength scratch frame count ceiling inputLimit
        atArray atIndex atMaximum entryPrefix inside4 inputBound limitBound scratchGlobal frameGlobal code orderedFrame
        framePositive scratchBelow arena bodyBudget value (by rw [bodyRun]; exact congrArg (fun r => (r,post)) returned)
      have checkedOne : shapeEqHOL (shapeOfHOLExact value) (.comb [.one,.one,.one,.one]) = true := by
        simpa only [Bool.and_self] using checked
      obtain ⟨first,second,third,fourth,rfl⟩ := value_four_words_of_checked_shape value checkedOne
      let resumed := setVarHOLFinite (ofString "r")
        (.rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]) {post with locals := state.locals}
      have resumedPrefix : RlpSliceInputPrefix resumed array input inputLength count.toNat := by
        intro slot inside
        obtain ⟨p,n,item⟩ := retained slot inside
        exact ⟨p,n,item.after_frame post resumed array slot p n input inputLength rfl rfl rfl⟩
      have resumedRecord : resumed.locals.lookup (ofString "a") = some (.val (.word record)) := by
        simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "r" ≠ ofString "a" by decide] using atRecord
      have resumedEntry : resumed.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]) := by
        simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "r" ≠ ofString "ent" by decide] using entryLocal
      have resumedValue : resumed.locals.lookup (ofString "r") =
          some (.rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]) := by
        simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      exact evaluate_authorization_r_store_and_last_bounded resumed record first second third fourth array count input inputLength
        scratch frame ceiling inputLimit resumedRecord resumedValue before fits resumedEntry resumedPrefix inside inputBound limitBound
        globals.1 globals.2 (metadata.1.trans code) orderedFrame framePositive scratchBelow
        (by change ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → post.memaddrs address
            intro address lower upper
            rw [metadata.2.1]
            exact arena address lower upper) arrayBelowFrame tailBudget

#print axioms evaluate_authorization_r_scalar_bounded
end InitECandidate.Runtime
