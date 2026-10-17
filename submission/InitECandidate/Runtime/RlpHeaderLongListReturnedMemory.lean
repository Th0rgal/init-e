import InitECandidate.Runtime.RlpHeaderLongListReadContract
import InitECandidate.Runtime.RlpReadLengthReadFrame
import InitECandidate.Runtime.PanDecCallReturnedMemory
import InitECandidate.Runtime.ReadOnlyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpHeader_long_list_finish_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state rlpHeaderLongListFinish = (some (.returned value),post)) :
    post.memory = state.memory := by
  rw [source_rlpHeader_long_list_finish] at run
  have tail := evaluate_rlp_error_checks_returned state post rlpItemLongChecks rlpHeaderLongListReturn value code run
  have frame := evaluate_readOnly_memory rlpHeaderLongListReturn (by rfl) state
  rw [tail] at frame
  exact frame

/-- Successful original long-list header length decoding and validation
preserve caller memory, including when no ticks remain for passing checks. -/
theorem rlpHeader_long_list_read_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer lengthBytes : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "ll") = some (.val (.word lengthBytes)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state rlpHeaderLongListRead = (some (.returned value),post)) :
    post.memory = state.memory := by
  let arguments : List (ExpHOL 64) := [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll")]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word (pointer + 1)),.val (.word lengthBytes)] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,lengthLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  have installed : state.code.lookup (ofString "rlp_read_length") =
      some ([(ofString "p",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_rlp_read_length,.one) := by
    rw [code]; exact originalRuntimeCode_rlpReadLength_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "rlp_read_length") (ofString "p") (ofString "n")
    (sourceFunctionBody Guest.guestFn_rlp_read_length) (pointer + 1) lengthBytes (by decide) installed
  rw [source_rlpHeader_long_list_read] at run
  apply evaluate_decCall_returned_memory state post (ofString "n") (ofString "rlp_read_length") .one .one
    arguments [.val (.word (pointer + 1)),.val (.word lengthBytes)]
    (sourceFunctionBody Guest.guestFn_rlp_read_length) rlpHeaderLongListFinish (rlpReadLengthCallee (pointer + 1) lengthBytes)
    value args lookup ?_ ?_ run
  · intro returned output evaluated
    have frame := evaluate_rlpReadLength_body_frame (callEntryStateHOLFinite state (rlpReadLengthCallee (pointer + 1) lengthBytes)) code
    rw [evaluated] at frame
    exact frame.1
  · intro ready output returned readyCode evaluated
    exact rlpHeader_long_list_finish_returned_memory (setVarHOLFinite (ofString "n") returned ready) output value
      (readyCode.trans code) evaluated

#print axioms rlpHeader_long_list_finish_returned_memory
#print axioms rlpHeader_long_list_read_returned_memory
end InitECandidate.Runtime
