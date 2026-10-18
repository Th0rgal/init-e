import InitECandidate.Runtime.TxFixedBytesInputBound
import InitECandidate.Runtime.OriginalTxFixedBytesCode
import InitECandidate.Runtime.PanThreeWordLookup
import InitECandidate.Runtime.PanDecCallCheckedContinuationBound
import InitECandidate.Runtime.AccessListKeysCopyBound
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original fixed-byte extraction and the access-list key copy continuation inherit a
common input budget from the concrete slice prefix. -/
theorem evaluate_txFixedBytes_access_keys_copy_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (buffer : BitVec 64)
    (bufferLocal : state.locals.lookup (ofString "keys") = some (.val (.word buffer)))
    (array index width input inputLength scratch frame : BitVec 64) (filled ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word array),.val (.word index),.val (.word width)])
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength filled) (inside : index.toNat < filled)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92650 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.decCall (ofString "k") .one (ofString "tx_fixed_bytes") arguments accessKeysCopy)
    state.clock ≤ evaluated.2.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92650) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := ((HolFiniteMapExact.empty.update (ofString "arr",.val (.word array))).update
    (ofString "i",.val (.word index))).update (ofString "width",.val (.word width))
  let entry := callEntryStateHOLFinite state callee
  have atArray : entry.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "width" ≠ ofString "arr" by decide,show ofString "i" ≠ ofString "arr" by decide]
  have atIndex : entry.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "width" ≠ ofString "i" by decide]
  have entryPrefix : RlpSliceInputPrefix entry array input inputLength filled := by
    intro slot bounded
    obtain ⟨p,n,item⟩ := valid slot bounded
    exact ⟨p,n,RlpSliceInputEntry.after_frame state entry array slot p n input inputLength item rfl rfl rfl⟩
  have bound := evaluate_txFixedBytes_input_bounded entry array index input inputLength scratch frame filled ceiling inputLimit
    atArray atIndex entryPrefix inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (by change inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ state.clock - 1; omega)
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_tx_fixed_bytes) with
  | mk bodyResult bodyPost =>
    rw [bodyRun] at bound
    dsimp only at bound
    have installed : state.code.lookup (ofString "tx_fixed_bytes") =
        some ([(ofString "arr",.one),(ofString "i",.one),(ofString "width",.one)],sourceFunctionBody Guest.guestFn_tx_fixed_bytes,.one) := by
      rw [code]; exact originalRuntimeCode_txFixedBytes_lookup
    have lookup := pan_three_word_lookup state.code.lookup (ofString "tx_fixed_bytes") (ofString "arr") (ofString "i") (ofString "width")
      (sourceFunctionBody Guest.guestFn_tx_fixed_bytes) array index width (by decide) (by decide) (by decide) installed
    have entryClock : entry.clock = state.clock - 1 := rfl
    have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_tx_fixed_bytes)
    rw [bodyRun] at metadata
    dsimp only at metadata
    have continuationBound : ∀ value, bodyResult = some (.returned value) →
        (shapeEqHOL (shapeOfHOLExact value) .one && shapeEqHOL (shapeOfHOLExact value) .one) = true →
        let resumed := setVarHOLFinite (ofString "k") value {bodyPost with locals := state.locals}
        let evaluated := evaluateHOLFiniteState resumed accessKeysCopy
        resumed.clock ≤ evaluated.2.clock + 16 ∧ evaluated.2.clock ≤ resumed.clock ∧ evaluated.1 ≠ some .timeOut := by
      intro value returned goodShape
      have wordShape : ∃ word : BitVec 64, value = .val (.word word) := by
        cases value with
        | val atom => cases atom with | word word => exact ⟨word,rfl⟩
        | rStruct fields => simp [shapeOfHOLExact,shapeEqHOL] at goodShape
        | nStruct name fields => simp [shapeOfHOLExact,shapeEqHOL] at goodShape
      obtain ⟨word,rfl⟩ := wordShape
      let resumed := setVarHOLFinite (ofString "k") (.val (.word word)) {bodyPost with locals := state.locals}
      have atBuffer : resumed.locals.lookup (ofString "keys") = some (.val (.word buffer)) := by
        simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "k" ≠ ofString "keys" by decide] using bufferLocal
      have atI : resumed.locals.lookup (ofString "j") = some (.val (.word index)) := by
        simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "k" ≠ ofString "j" by decide] using indexLocal
      have atSource : resumed.locals.lookup (ofString "k") = some (.val (.word word)) := by
        simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      exact evaluate_access_keys_copy_bounded resumed buffer index word atBuffer atI atSource (metadata.1.trans code)
        (by change 16 ≤ bodyPost.clock; have cost := bound.1; omega)
    have combined := evaluate_decCall_checked_continuation_bounded state bodyPost (ofString "k") (ofString "tx_fixed_bytes") .one .one arguments
      [.val (.word array),.val (.word index),.val (.word width)] (sourceFunctionBody Guest.guestFn_tx_fixed_bytes) accessKeysCopy callee bodyResult
      (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634) 16 args lookup (by omega) bodyRun bound.2.1
      (by omega) bound.2.2 continuationBound
    simpa only [Nat.add_assoc] using combined

#print axioms evaluate_txFixedBytes_access_keys_copy_bounded
end InitECandidate.Runtime
