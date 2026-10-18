import InitECandidate.Runtime.TxFixedBytesIndependentOuterPrefix
import InitECandidate.Runtime.AccessListKeysStepBound
import InitECandidate.Runtime.TxFixedBytesInputPrefix
import InitECandidate.Runtime.PanDecCallNormalWordMemoryClock
import InitECandidate.Runtime.AccessListKeysCopyInputPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem access_keys_step_normal_independent_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count index buffer input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (listLocal : state.locals.lookup (ofString "slots") = some (.rStruct [.val (.word array),.val (.word count)]))
    (bufferLocal : state.locals.lookup (ofString "keys") = some (.val (.word buffer)))
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92650 ≤ state.clock)
    (aligned : buffer.toNat % 8 = 0) (fits : buffer.toNat + index.toNat * 32 + 32 ≤ 2^64)
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerBeforeFrame : outerArray.toNat + outerCount.toNat * 16 ≤ frame.toNat)
    (outerBeforeBuffer : outerArray.toNat + outerCount.toNat * 16 ≤ buffer.toNat)
    (run : evaluateHOLFiniteState state accessKeysStep = (none,post)) :
    RlpSliceInputPrefix post outerArray outerInput outerLength outerCount.toNat := by
  let arguments : List (ExpHOL 64) := [.rfield 0 (.var .local (ofString "slots")),.var .local (ofString "j"),.const 32]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word array),.val (.word index),.val (.word (32 : BitVec 64))] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,listLocal,indexLocal]
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := ((HolFiniteMapExact.empty.update (ofString "arr",.val (.word array))).update
    (ofString "i",.val (.word index))).update (ofString "width",.val (.word 32))
  let entry := callEntryStateHOLFinite state callee
  have atArray : entry.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "width" ≠ ofString "arr" by decide,show ofString "i" ≠ ofString "arr" by decide]
  have atIndex : entry.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "width" ≠ ofString "i" by decide]
  have entryPrefix : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro slot bounded
    obtain ⟨p,n,item⟩ := valid slot bounded
    exact ⟨p,n,RlpSliceInputEntry.after_frame state entry array slot p n input inputLength item rfl rfl rfl⟩
  have installed : state.code.lookup (ofString "tx_fixed_bytes") =
      some ([(ofString "arr",.one),(ofString "i",.one),(ofString "width",.one)],sourceFunctionBody Guest.guestFn_tx_fixed_bytes,.one) := by
    rw [code]; exact originalRuntimeCode_txFixedBytes_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "tx_fixed_bytes") (ofString "arr") (ofString "i") (ofString "width")
    (sourceFunctionBody Guest.guestFn_tx_fixed_bytes) array index 32 (by decide) (by decide) (by decide) installed
  have source : accessKeysStep = .decCall (ofString "k") .one (ofString "tx_fixed_bytes") arguments accessKeysCopy := by
    exact source_access_keys_step
  rw [source] at run
  obtain ⟨word,bodyPost,ready,output,bodyRun,locals,globals,readyCode,memory,domain,clock,tail,restored⟩ := evaluate_decCall_one_normal_word_memory_clock
    state post (ofString "k") (ofString "tx_fixed_bytes") arguments _ _ accessKeysCopy callee args lookup run
  have outerEntry : RlpSliceInputPrefix entry outerArray outerInput outerLength outerCount.toNat := by
    intro slot within
    obtain ⟨p,n,item⟩ := outerValid slot within
    exact ⟨p,n,item.after_frame state entry outerArray slot p n outerInput outerLength rfl rfl rfl⟩
  have retained := txFixedBytes_input_returned_independent_outer_prefix entry bodyPost array index input inputLength scratch frame count ceiling inputLimit
    atArray atIndex entryPrefix inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (by change inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ state.clock - 1; omega) (.val (.word word)) bodyRun outerArray outerCount outerInput outerLength outerEntry outerBeforeFrame
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_tx_fixed_bytes)
  rw [bodyRun] at metadata
  dsimp only at metadata
  let resumed := setVarHOLFinite (ofString "k") (.val (.word word)) ready
  have atBuffer : resumed.locals.lookup (ofString "keys") = some (.val (.word buffer)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,show ofString "k" ≠ ofString "keys" by decide] using bufferLocal
  have atI : resumed.locals.lookup (ofString "j") = some (.val (.word index)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,show ofString "k" ≠ ofString "j" by decide] using indexLocal
  have atSource : resumed.locals.lookup (ofString "k") = some (.val (.word word)) := by
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bodyBound := evaluate_txFixedBytes_input_bounded entry array index input inputLength scratch frame count.toNat ceiling inputLimit
    atArray atIndex entryPrefix inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (by change inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ state.clock - 1; omega)
  rw [bodyRun] at bodyBound
  have resumedPrefix : RlpSliceInputPrefix resumed outerArray outerInput outerLength outerCount.toNat := by
    intro slot bounded
    obtain ⟨p,n,item⟩ := retained slot bounded
    exact ⟨p,n,RlpSliceInputEntry.after_frame bodyPost resumed outerArray slot p n outerInput outerLength item domain (congrFun memory _) (congrFun memory _)⟩
  have copied := access_keys_copy_normal_input_prefix resumed output buffer index word outerArray outerCount outerInput outerLength atBuffer atI atSource
    (readyCode.trans (metadata.1.trans code)) resumedPrefix outerBeforeBuffer aligned fits
    (by
      change 16 ≤ ready.clock
      rw [clock]
      have cost := bodyBound.1
      change state.clock - 1 ≤ bodyPost.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633) at cost
      omega) tail
  rw [restored]
  intro slot bounded
  obtain ⟨p,n,item⟩ := copied slot bounded
  exact ⟨p,n,RlpSliceInputEntry.after_frame output _ outerArray slot p n outerInput outerLength item rfl rfl rfl⟩

#print axioms access_keys_step_normal_independent_outer_prefix
end InitECandidate.Runtime
