import InitECandidate.Runtime.RlpItemTotalBodyProgress
import InitECandidate.Runtime.RlpItemTotalContinuationNamedGlobal
import InitECandidate.Runtime.PanDecCallReturnedGlobalClockScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful complete original item-total execution retains its entry
scratch/frame globals through header parsing, list validation and return scope. -/
theorem rlpItemTotal_body_returned_named_global {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (watched : MlS) (different : ofString "scratch_ptr" ≠ watched)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : (2 * length.toNat + 1) * 15 + 17 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item_total) = (some (.returned value),post)) :
    post.globals.lookup watched = state.globals.lookup watched := by
  let arguments : List (ExpHOL 64) := [.var .local (ofString "p"),.var .local (ofString "len")]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,lengthLocal]
  have installed : state.code.lookup (ofString "rlp_item_header") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_item_header,.comb [.one,.one,.one]) := by
    rw [code]; exact originalRuntimeCode_rlpHeader_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_item_header")
    (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn_rlp_item_header) (.comb [.one,.one,.one])
    pointer length (by decide) installed
  rw [source_rlpItemTotal_body] at run
  obtain ⟨parsed,bodyPost,ready,output,bodyRun,locals,globals,readyClock,domain,_,readyCode,tail,restored⟩ := evaluate_decCall_returned_global_clock_scope state post
    (ofString "h") (ofString "rlp_item_header") (.comb [.one,.one,.one]) (.comb [.one,.one,.one]) arguments
    [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_rlp_item_header) rlpItemTotalContinuation
    (rlpHeaderCallee pointer length) value args lookup run
  let entry := callEntryStateHOLFinite state (rlpHeaderCallee pointer length)
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryTicks : 11 ≤ entry.clock := by change 11 ≤ state.clock - 1; omega
  have valid : RlpHeaderSizedProgress parsed length :=
    ⟨rlpHeader_uniform_return_progress entry bodyPost pointer length parsed atPointer atLength code entryTicks bodyRun,
      rlpHeader_uniform_return_sizes entry bodyPost pointer length parsed atPointer atLength code entryTicks bodyRun⟩
  have headerGlobals := rlpHeader_uniform_returned_globals entry bodyPost pointer length parsed atPointer atLength code entryTicks bodyRun
  have headerBound := evaluate_rlpHeader_uniform_bounded entry pointer length atPointer atLength code entryTicks
  rw [bodyRun] at headerBound
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_item_header)
  rw [bodyRun] at metadata
  obtain ⟨header,payload,kind,shape,_,_,_⟩ := valid.2
  subst parsed
  let entered := setVarHOLFinite (ofString "h")
    (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)]) ready
  have atCallerPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "h" ≠ ofString "p" by decide] using pointerLocal
  have atHeader : entered.locals.lookup (ofString "h") = some
      (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)]) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atScratch : entered.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) := by
    change ready.globals.lookup _ = _
    rw [globals,headerGlobals]; exact scratchGlobal
  have atFrame : entered.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
    change ready.globals.lookup _ = _
    rw [globals,headerGlobals]; exact frameGlobal
  have enteredArena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → entered.memaddrs address := by
    intro address lower upper
    change ready.memaddrs address
    rw [domain,metadata.2.1]
    exact arena address lower upper
  have result := rlpItemTotal_continuation_returned_named_global entered output watched different pointer length header payload kind scratch frame ceiling inputLimit
    atCallerPointer atHeader valid noWrap lengthBound limitBound atScratch atFrame (readyCode.trans (metadata.1.trans code))
    orderedFrame framePositive scratchBelow enteredArena (by
      change (2 * length.toNat + 1) * 15 + 5 ≤ ready.clock
      have entryClock : entry.clock = state.clock - 1 := rfl
      dsimp only at headerBound
      omega) value tail
  rw [restored]
  simpa only [entered,setVarHOLFinite,globals,headerGlobals,entry,callEntryStateHOLFinite] using result

#print axioms rlpItemTotal_body_returned_named_global
end InitECandidate.Runtime
