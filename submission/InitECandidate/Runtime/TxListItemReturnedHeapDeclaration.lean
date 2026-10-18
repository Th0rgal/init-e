import InitECandidate.Runtime.TxListItemHeapIndependentOuterPrefix
import InitECandidate.Runtime.TxListItemInputBound
import InitECandidate.Runtime.TxListItemInputRange
import InitECandidate.Runtime.TxListItemInputGlobals
import InitECandidate.Runtime.TxListItemInputNamedGlobal
import InitECandidate.Runtime.OriginalTxListItemCode
import InitECandidate.Runtime.PanDecCallReturnedGlobalMemoryClockScope
import InitECandidate.Runtime.PanTwoWordLookup
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A real returned list-item declaration reaches its arbitrary continuation
with a bounded input subinterval and the independent heap prefix intact. No
future allocation or below-frame heap reserve is assumed. -/
theorem txListItem_returned_heap_declaration {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (continuation : ProgHOL 64) (arguments : List (ExpHOL 64))
    (array index input inputLength scratch frame : BitVec 64) (filled ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word array),.val (.word index)])
    (valid : RlpSliceInputPrefix state array input inputLength filled) (inside : index.toNat < filled)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634 ≤ state.clock)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedFits : watchedArray.toNat + watchedCount.toNat * 16 ≤ 2^64)
    (watchedAbove : ceiling ≤ watchedArray.toNat)
    (finalValue : ValueHOL 64)
    (run : evaluateHOLFiniteState state (.decCall name (.comb [.one,.one]) (ofString "tx_list_item") arguments continuation) =
      (some (.returned finalValue),post)) :
    ∃ (pointer length : BitVec 64) (ready output : PanSemStateFiniteExact 64 F),
      input.toNat ≤ pointer.toNat ∧ pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat ∧
      pointer.toNat + length.toNat < 2^64 ∧ length.toNat ≤ inputLength.toNat ∧
      ready.locals = state.locals ∧ RlpSliceInputPrefix ready watchedArray watchedInput watchedLength watchedCount.toNat ∧
      ready.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      ready.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      ready.globals.lookup (ofString "heap_ptr") = state.globals.lookup (ofString "heap_ptr") ∧
      ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧
      state.clock ≤ ready.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634) ∧
      ready.clock ≤ state.clock ∧
      evaluateHOLFiniteState (setVarHOLFinite name (.rStruct [.val (.word pointer),.val (.word length)]) ready) continuation =
        (some (.returned finalValue),output) ∧
      post = {output with locals := HolFiniteMapExact.resVarEq output.locals (name,state.locals.lookup name)} := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "arr",.val (.word array))).update (ofString "i",.val (.word index))
  let entry := callEntryStateHOLFinite state callee
  have atArray : entry.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "arr" by decide]
  have atIndex : entry.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryValid : RlpSliceInputPrefix entry array input inputLength filled := by
    intro slot bounded
    obtain ⟨p,n,item⟩ := valid slot bounded
    exact ⟨p,n,item.after_frame state entry _ _ _ _ _ _ rfl rfl rfl⟩
  have entryWatched : RlpSliceInputPrefix entry watchedArray watchedInput watchedLength watchedCount.toNat := by
    intro slot bounded
    obtain ⟨p,n,item⟩ := watchedValid slot bounded
    exact ⟨p,n,item.after_frame state entry _ _ _ _ _ _ rfl rfl rfl⟩
  have installed : state.code.lookup (ofString "tx_list_item") =
      some ([(ofString "arr",.one),(ofString "i",.one)],sourceFunctionBody Guest.guestFn_tx_list_item,.comb [.one,.one]) := by
    rw [code]; exact originalRuntimeCode_txListItem_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "tx_list_item") (ofString "arr") (ofString "i")
    (sourceFunctionBody Guest.guestFn_tx_list_item) (.comb [.one,.one]) array index (by decide) installed
  obtain ⟨value,bodyPost,ready,output,bodyRun,locals,memory,globals,clock,domain,_,readyCode,tail,restored⟩ :=
    evaluate_decCall_returned_global_memory_clock_scope state post name (ofString "tx_list_item") (.comb [.one,.one]) (.comb [.one,.one])
      arguments [.val (.word array),.val (.word index)] (sourceFunctionBody Guest.guestFn_tx_list_item) continuation callee finalValue args lookup run
  have ticks : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ entry.clock := by
    change _ ≤ state.clock - 1
    omega
  obtain ⟨pointer,length,shape,starts,ends,noWrap,lengthBound⟩ := txListItem_input_returned_range entry bodyPost
    array index input inputLength filled atArray atIndex entryValid inside (by omega) code (by omega) value bodyRun
  have keptGlobals := txListItem_input_returned_globals entry bodyPost array index input inputLength scratch frame filled ceiling inputLimit
    atArray atIndex entryValid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena ticks value bodyRun
  have heapFrame := txListItem_input_returned_named_global entry bodyPost (ofString "heap_ptr") (by decide)
    array index input inputLength scratch frame filled ceiling inputLimit atArray atIndex entryValid inside inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena ticks value bodyRun
  have kept := txListItem_input_returned_heap_independent_outer_prefix entry bodyPost array index input inputLength scratch frame filled ceiling inputLimit
    atArray atIndex entryValid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena ticks value bodyRun
    watchedArray watchedCount watchedInput watchedLength entryWatched watchedFits watchedAbove
  have bounded := evaluate_txListItem_input_bounded entry array index input inputLength scratch frame filled ceiling inputLimit
    atArray atIndex entryValid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena ticks
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_tx_list_item)
  rw [bodyRun] at bounded metadata
  dsimp only at bounded metadata
  have retained : RlpSliceInputPrefix ready watchedArray watchedInput watchedLength watchedCount.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := kept slot inside
    exact ⟨p,n,item.after_frame bodyPost ready _ _ _ _ _ _ domain (congrFun memory _) (congrFun memory _)⟩
  subst value
  refine ⟨pointer,length,ready,output,starts,ends,noWrap,lengthBound,locals,retained,?_,?_,?_,readyCode.trans metadata.1,domain.trans metadata.2.1,?_,?_,tail,restored⟩
  · rw [globals]; exact keptGlobals.1
  · rw [globals]; exact keptGlobals.2
  · rw [globals]; exact heapFrame
  · rw [clock]
    have debit : state.clock - 1 ≤ bodyPost.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633) := bounded.1
    omega
  · rw [clock]
    exact bounded.2.1.trans (Nat.sub_le _ _)

#print axioms txListItem_returned_heap_declaration
end InitECandidate.Runtime
