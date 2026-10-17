import InitECandidate.Runtime.RlpItemLongListInputBound
import InitECandidate.Runtime.RlpReadLengthReadFrame
import InitECandidate.Runtime.RlpReadLengthCallResult
import InitECandidate.Runtime.PanDecCallContinuationBound
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpItemLongListBody : ProgHOL 64 :=
  match rlpItemLongList with
  | .dec _ _ _ body => body
  | _ => .skip

def rlpItemLongListRead : ProgHOL 64 :=
  match rlpItemLongListBody with
  | .seq _ body => body
  | _ => .skip

theorem source_rlpItem_long_list_read : rlpItemLongListRead =
    .decCall (ofString "n") .one (ofString "rlp_read_length")
      [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll")] rlpItemLongListFinish := by
  simp only [rlpItemLongListRead,rlpItemLongListFinish,rlpItemLongListBody,rlpItemLongList,rlpItemAfterLongString,rlpItemAfterShortString,
    rlpItemAfterSingleByte,rlpItemAfterByte,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual long-list length-reader call composes with an input-quadratic
finish budget, covering all callee and continuation error paths. -/
theorem evaluate_rlpItem_long_list_read_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer total headerLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (inputRange : pointer.toNat + total.toNat < 2^64)
    (headerFits : 1 + headerLength.toNat ≤ total.toNat)
    (lengthBound : total.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (ticks : headerLength.toNat + 2 + (total.toNat * ((2 * total.toNat + 1) * 15 + 19) + 1) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpItemLongListRead
    state.clock ≤ evaluated.2.clock + (headerLength.toNat + 2 + (total.toNat * ((2 * total.toNat + 1) * 15 + 19) + 1)) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let arguments : List (ExpHOL 64) := [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll")]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word (pointer + 1)),.val (.word headerLength)] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  let callee := rlpReadLengthCallee (pointer + 1) headerLength
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word (pointer + 1))) := by
    simp [entry,callee,rlpReadLengthCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "n" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "n") = some (.val (.word headerLength)) := by
    simp [entry,callee,rlpReadLengthCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨result,post,run,cost,remaining,noTimeout,returned⟩ := evaluate_rlpReadLength_body_bounded entry
    (pointer + 1) headerLength atPointer atLength code (by change headerLength.toNat + 1 ≤ state.clock - 1; omega)
  have entryClock : entry.clock = state.clock - 1 := rfl
  have installed : state.code.lookup (ofString "rlp_read_length") =
      some ([(ofString "p",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_rlp_read_length,.one) := by
    rw [code]; exact originalRuntimeCode_rlpReadLength_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "rlp_read_length")
    (ofString "p") (ofString "n") (sourceFunctionBody Guest.guestFn_rlp_read_length) (pointer + 1) headerLength (by decide) installed
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_read_length)
  rw [run] at metadata
  dsimp only at metadata
  have preserved := evaluate_rlpReadLength_body_frame entry code
  rw [run] at preserved
  dsimp only at preserved
  have continuationBound : ∀ value, result = some (.returned value) →
      let resumed := setVarHOLFinite (ofString "n") value {post with locals := state.locals}
      let evaluated := evaluateHOLFiniteState resumed rlpItemLongListFinish
      resumed.clock ≤ evaluated.2.clock + (total.toNat * ((2 * total.toNat + 1) * 15 + 19) + 1) ∧ evaluated.2.clock ≤ resumed.clock ∧ evaluated.1 ≠ some .timeOut := by
    intro value equal
    obtain ⟨word,rfl⟩ := returned value equal
    let resumed := setVarHOLFinite (ofString "n") (.val (.word word)) {post with locals := state.locals}
    have atP : resumed.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
      simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "n" ≠ ofString "p" by decide] using pointerLocal
    have atLL : resumed.locals.lookup (ofString "ll") = some (.val (.word headerLength)) := by
      simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "n" ≠ ofString "ll" by decide] using headerLocal
    have atN : resumed.locals.lookup (ofString "n") = some (.val (.word word)) := by
      simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have atTotal : resumed.locals.lookup (ofString "len") = some (.val (.word total)) := by
      simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "n" ≠ ofString "len" by decide] using totalLocal
    have atScratch : resumed.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) := by
      change post.globals.lookup _ = _
      rw [preserved.2]
      exact scratchGlobal
    have atFrame : resumed.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
      change post.globals.lookup _ = _
      rw [preserved.2]
      exact frameGlobal
    have atArena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → resumed.memaddrs address := by
      intro address low high
      change post.memaddrs address
      rw [metadata.2.1]
      exact arena address low high
    exact evaluate_rlpItem_long_list_uniform_finish_bounded resumed pointer total headerLength word scratch frame ceiling inputLimit
      atP atLL atN atTotal inputRange headerFits lengthBound limitBound atScratch atFrame
      (metadata.1.trans code) orderedFrame framePositive scratchBelow atArena
      (by change (total.toNat * ((2 * total.toNat + 1) * 15 + 19) + 1) ≤ post.clock; omega)
  have bound := evaluate_decCall_continuation_bounded state post (ofString "n") (ofString "rlp_read_length")
    .one .one arguments [.val (.word (pointer + 1)),.val (.word headerLength)]
    (sourceFunctionBody Guest.guestFn_rlp_read_length) rlpItemLongListFinish callee result (headerLength.toNat + 2) (total.toNat * ((2 * total.toNat + 1) * 15 + 19) + 1)
    args lookup (by omega) run remaining (by omega) noTimeout continuationBound
  rw [source_rlpItem_long_list_read]
  exact bound

#print axioms evaluate_rlpItem_long_list_read_bounded
theorem evaluate_rlpItem_long_list_read_terminal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer headerLength : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (code : state.code = originalRuntimeCode) (ticks : headerLength.toNat + 2 ≤ state.clock) :
    (evaluateHOLFiniteState state rlpItemLongListRead).1 ≠ none := by
  intro normal
  cases run : evaluateHOLFiniteState state rlpItemLongListRead with
  | mk result post =>
    rw [run] at normal
    change result = none at normal
    subst result
    rw [source_rlpItem_long_list_read] at run
    have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll")] =
        some [.val (.word (pointer + 1)),.val (.word headerLength)] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    obtain ⟨word,ready,output,_,tail,_⟩ := evaluate_rlpReadLength_decCall_normal state post (ofString "n")
      [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll")]
      rlpItemLongListFinish (pointer + 1) headerLength args code ticks run
    have terminal := evaluate_rlpItem_long_list_finish_terminal (setVarHOLFinite (ofString "n") (.val (.word word)) ready)
    rw [tail] at terminal
    exact terminal rfl

#print axioms evaluate_rlpItem_long_list_read_terminal
end InitECandidate.Runtime
