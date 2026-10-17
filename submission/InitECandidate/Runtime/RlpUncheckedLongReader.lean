import InitECandidate.Runtime.RlpUncheckedLengthReturnBody
import InitECandidate.Runtime.RlpUncheckedSource
import InitECandidate.Runtime.PanDecWordResultScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful original long-string branch exposes its concrete reader
execution and exact total encoded size through local-scope restoration. -/
theorem rlpUnchecked_long_string_returned_reader {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (code : state.code = originalRuntimeCode) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state rlpUncheckedLongString = (some (.returned value),post)) :
    ∃ (decoded : BitVec 64) (readerPost : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState (callEntryStateHOLFinite
        (setVarHOLFinite (ofString "ll") (.val (.word (header - 183))) state)
        (rlpReadLengthCallee (pointer + 1) (header - 183))) (sourceFunctionBody Guest.guestFn_rlp_read_length) =
          (some (.returned (.val (.word decoded))),readerPost) ∧
      value = .val (.word (1 + ((header - 183) + decoded))) := by
  let entered := setVarHOLFinite (ofString "ll") (.val (.word (header - 183))) state
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ll" ≠ ofString "p" by decide] using pointerLocal
  have atLength : entered.locals.lookup (ofString "ll") = some (.val (.word (header - 183))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have args : evalListHOLFinite entered (h := fun address => Classical.propDecidable (entered.memaddrs address))
      [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll")] =
      some [.val (.word (pointer + 1)),.val (.word (header - 183))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atPointer,atLength,wordOpHOL,wordOp,valueIsWord,valueWord]
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 183]) = some (.val (.word (header - 183))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpUnchecked_long_string] at run
  obtain ⟨output,tail,_⟩ := evaluate_dec_word_result_scope state post (ofString "ll")
    (.op .sub [.var .local (ofString "b"),.const 183]) (header - 183) _ (some (.returned value)) initializer run
  exact rlpUnchecked_length_declaration_return_body entered output (ofString "ll") (ofString "n") (by decide)
    [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll")]
    (pointer + 1) (header - 183) value atLength args code tail

#print axioms rlpUnchecked_long_string_returned_reader

/-- A successful original long-list branch exposes its concrete reader
execution and exact total encoded size through local-scope restoration. -/
theorem rlpUnchecked_long_list_returned_reader {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (code : state.code = originalRuntimeCode) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state rlpUncheckedLongList = (some (.returned value),post)) :
    ∃ (decoded : BitVec 64) (readerPost : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState (callEntryStateHOLFinite
        (setVarHOLFinite (ofString "ll2") (.val (.word (header - 247))) state)
        (rlpReadLengthCallee (pointer + 1) (header - 247))) (sourceFunctionBody Guest.guestFn_rlp_read_length) =
          (some (.returned (.val (.word decoded))),readerPost) ∧
      value = .val (.word (1 + ((header - 247) + decoded))) := by
  let entered := setVarHOLFinite (ofString "ll2") (.val (.word (header - 247))) state
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ll2" ≠ ofString "p" by decide] using pointerLocal
  have atLength : entered.locals.lookup (ofString "ll2") = some (.val (.word (header - 247))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have args : evalListHOLFinite entered (h := fun address => Classical.propDecidable (entered.memaddrs address))
      [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll2")] =
      some [.val (.word (pointer + 1)),.val (.word (header - 247))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atPointer,atLength,wordOpHOL,wordOp,valueIsWord,valueWord]
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 247]) = some (.val (.word (header - 247))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpUnchecked_long_list] at run
  obtain ⟨output,tail,_⟩ := evaluate_dec_word_result_scope state post (ofString "ll2")
    (.op .sub [.var .local (ofString "b"),.const 247]) (header - 247) _ (some (.returned value)) initializer run
  exact rlpUnchecked_length_declaration_return_body entered output (ofString "ll2") (ofString "n2") (by decide)
    [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll2")]
    (pointer + 1) (header - 247) value atLength args code tail

#print axioms rlpUnchecked_long_list_returned_reader

end InitECandidate.Runtime
