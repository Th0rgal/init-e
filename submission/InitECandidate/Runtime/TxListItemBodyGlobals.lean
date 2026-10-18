import InitECandidate.Runtime.TxListItemBodyBound
import InitECandidate.Runtime.RlpItemBodyGlobals
import InitECandidate.Runtime.PanDecCallReturnedGlobalClockScope
import InitECandidate.Runtime.NamedGlobalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem txListItem_body_returned_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) txListItemArguments =
      some [.val (.word pointer),.val (.word length)])
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92633 ≤ state.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_tx_list_item) = (some (.returned value),post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "len" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have installed : state.code.lookup (ofString "rlp_item") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_item,.comb [.one,.one,.one,.one]) := by
    rw [code]; exact originalRuntimeCode_rlpItem_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_item") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_item) (.comb [.one,.one,.one,.one]) pointer length (by decide) installed
  rw [source_txListItem_body] at run
  obtain ⟨parsed,bodyPost,ready,output,bodyRun,_,globals,_,_,_,_,tail,restored⟩ := evaluate_decCall_returned_global_clock_scope
    state post (ofString "it") (ofString "rlp_item") (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one])
    txListItemArguments [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_rlp_item)
    txListItemContinuation callee value args lookup run
  have retained := rlpItem_body_returned_globals entry bodyPost pointer length scratch frame ceiling inputLimit atPointer atLength
    noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (by change length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92632 ≤ state.clock - 1; omega) parsed bodyRun
  have frame : ∀ watched : MlS, output.globals.lookup watched = bodyPost.globals.lookup watched := by
    intro watched
    have supported : avoidsGlobalAssignment watched txListItemContinuation = true := by
      rw [source_txListItem_continuation]; rfl
    have same := evaluate_avoidsGlobalAssignment watched txListItemContinuation supported
      (setVarHOLFinite (ofString "it") parsed ready)
    rw [tail] at same
    exact same.trans (congrArg (fun g => g.lookup watched) globals)
  rw [restored]
  exact ⟨(frame _).trans retained.1,(frame _).trans retained.2⟩

#print axioms txListItem_body_returned_globals
end InitECandidate.Runtime
