import InitECandidate.Runtime.RlpItemLongBodyBound
import InitECandidate.Runtime.RlpItemLongReadBound
import InitECandidate.Runtime.RlpReadLengthReadFrame
import InitECandidate.Runtime.RlpErrorChecksReturnFlow
import InitECandidate.Runtime.ReadOnlyGlobals
import InitECandidate.Runtime.PanDecCallReturnedGlobals
import InitECandidate.Runtime.PanDecWordResultScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpItem_long_finish_returned_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state rlpItemLongFinish = (some (.returned value),post)) :
    post.globals = state.globals := by
  rw [source_rlpItem_long_finish] at run
  have tail := evaluate_rlp_error_checks_returned_tail state post rlpItemLongChecks rlpItemLongReturn value code run
  have globals := evaluate_readOnly_globals rlpItemLongReturn (by decide) state
  rw [tail] at globals
  exact globals

theorem rlpItem_long_read_returned_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer headerLength : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state rlpItemLongRead = (some (.returned value),post)) :
    post.globals = state.globals := by
  let arguments : List (ExpHOL 64) := [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll")]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word (pointer + 1)),.val (.word headerLength)] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,headerLocal,
      wordOpHOL,wordOp,valueIsWord,valueWord]
  have installed : state.code.lookup (ofString "rlp_read_length") =
      some ([(ofString "p",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_rlp_read_length,.one) := by
    rw [code]; exact originalRuntimeCode_rlpReadLength_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "rlp_read_length") (ofString "p") (ofString "n")
    (sourceFunctionBody Guest.guestFn_rlp_read_length) (pointer + 1) headerLength (by decide) installed
  rw [source_rlpItem_long_read] at run
  apply evaluate_decCall_returned_globals state post (ofString "n") (ofString "rlp_read_length") .one .one
    arguments [.val (.word (pointer + 1)),.val (.word headerLength)] (sourceFunctionBody Guest.guestFn_rlp_read_length)
    rlpItemLongFinish (rlpReadLengthCallee (pointer + 1) headerLength) value args lookup _ _ run
  · intro parsed output bodyRun
    have globals := evaluate_rlpReadLength_body_frame (callEntryStateHOLFinite state (rlpReadLengthCallee (pointer + 1) headerLength)) code
    rw [bodyRun] at globals
    exact globals.2
  · intro ready output parsed readyCode tail
    exact rlpItem_long_finish_returned_globals (setVarHOLFinite (ofString "n") parsed ready) output value (readyCode.trans code) tail

#print axioms rlpItem_long_finish_returned_globals
#print axioms rlpItem_long_read_returned_globals

theorem rlpItem_long_body_returned_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer headerLength : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state rlpItemLongBody = (some (.returned value),post)) :
    post.globals = state.globals := by
  obtain ⟨result,middle,checked,normal,noReturn⟩ := evaluate_rlp_error_check_flow state
    (.cmp .lower (.op .sub [.var .local (ofString "len"),.const 1]) (.var .local (ofString "ll"))) 3 code
  rw [source_rlpItem_long_body,evaluateHOLFiniteState_seq_line780,checked] at run
  cases result with
  | some stopped => exact False.elim (noReturn value (Prod.mk.inj run).1)
  | none =>
    have same := normal rfl
    subst middle
    exact rlpItem_long_read_returned_globals state post pointer headerLength value pointerLocal headerLocal code run

#print axioms rlpItem_long_body_returned_globals

theorem rlpItem_long_string_returned_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state rlpItemLongString = (some (.returned value),post)) :
    post.globals = state.globals := by
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 183]) = some (.val (.word (header - 183))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpItem_long_string] at run
  obtain ⟨output,bodyRun,restored⟩ := evaluate_dec_word_result_scope state post (ofString "ll")
    (.op .sub [.var .local (ofString "b"),.const 183]) (header - 183) rlpItemLongBody
    (some (.returned value)) initializer run
  let entered := setVarHOLFinite (ofString "ll") (.val (.word (header - 183))) state
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ll" ≠ ofString "p" by decide] using pointerLocal
  have atLength : entered.locals.lookup (ofString "ll") = some (.val (.word (header - 183))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have globals := rlpItem_long_body_returned_globals entered output pointer (header - 183) value atPointer atLength code bodyRun
  rw [restored]
  exact globals

#print axioms rlpItem_long_string_returned_globals
end InitECandidate.Runtime
