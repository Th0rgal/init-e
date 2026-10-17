import InitECandidate.Runtime.RlpUncheckedLongBound
import InitECandidate.Runtime.PanDecWordResultScope
import InitECandidate.Runtime.PanSequenceTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_rlpUnchecked_long_string_terminal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (code : state.code = originalRuntimeCode) (ticks : (header - 183).toNat + 2 ≤ state.clock) :
    (evaluateHOLFiniteState state rlpUncheckedLongString).1 ≠ none := by
  intro normal
  cases run : evaluateHOLFiniteState state rlpUncheckedLongString with
  | mk result post =>
    rw [run] at normal
    change result = none at normal
    subst result
    have initializer : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.op .sub [.var .local (ofString "b"),.const 183]) = some (.val (.word (header - 183))) := by
      simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    rw [source_rlpUnchecked_long_string] at run
    obtain ⟨output,bodyRun,_⟩ := evaluate_dec_word_result_scope state post (ofString "ll")
      (.op .sub [.var .local (ofString "b"),.const 183]) (header - 183)
      (.decCall (ofString "n") .one (ofString "rlp_read_length") [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll")] (.return (.op .add [.const 1,.var .local (ofString "ll"),.var .local (ofString "n")]))) none initializer run
    let entered := setVarHOLFinite (ofString "ll") (.val (.word (header - 183))) state
    have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
      simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "ll" ≠ ofString "p" by decide] using pointerLocal
    have atLength : entered.locals.lookup (ofString "ll") = some (.val (.word (header - 183))) := by
      simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have args : evalListHOLFinite entered (h := fun address => Classical.propDecidable (entered.memaddrs address)) [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll")] =
        some [.val (.word (pointer + 1)),.val (.word (header - 183))] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atPointer,atLength,wordOpHOL,wordOp,valueIsWord,valueWord]
    obtain ⟨word,ready,final,_,tailRun,_⟩ := evaluate_rlpReadLength_decCall_normal entered output (ofString "n")
      [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll")] (.return (.op .add [.const 1,.var .local (ofString "ll"),.var .local (ofString "n")])) (pointer + 1) (header - 183) args code ticks bodyRun
    have terminal := evaluate_return_terminal (setVarHOLFinite (ofString "n") (.val (.word word)) ready)
      (.op .add [.const 1,.var .local (ofString "ll"),.var .local (ofString "n")])
    rw [tailRun] at terminal
    exact terminal rfl

#print axioms evaluate_rlpUnchecked_long_string_terminal
theorem evaluate_rlpUnchecked_long_list_terminal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (code : state.code = originalRuntimeCode) (ticks : (header - 247).toNat + 2 ≤ state.clock) :
    (evaluateHOLFiniteState state rlpUncheckedLongList).1 ≠ none := by
  intro normal
  cases run : evaluateHOLFiniteState state rlpUncheckedLongList with
  | mk result post =>
    rw [run] at normal
    change result = none at normal
    subst result
    have initializer : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.op .sub [.var .local (ofString "b"),.const 247]) = some (.val (.word (header - 247))) := by
      simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    rw [source_rlpUnchecked_long_list] at run
    obtain ⟨output,bodyRun,_⟩ := evaluate_dec_word_result_scope state post (ofString "ll2")
      (.op .sub [.var .local (ofString "b"),.const 247]) (header - 247)
      (.decCall (ofString "n2") .one (ofString "rlp_read_length") [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll2")] (.return (.op .add [.const 1,.var .local (ofString "ll2"),.var .local (ofString "n2")]))) none initializer run
    let entered := setVarHOLFinite (ofString "ll2") (.val (.word (header - 247))) state
    have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
      simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "ll2" ≠ ofString "p" by decide] using pointerLocal
    have atLength : entered.locals.lookup (ofString "ll2") = some (.val (.word (header - 247))) := by
      simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have args : evalListHOLFinite entered (h := fun address => Classical.propDecidable (entered.memaddrs address)) [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll2")] =
        some [.val (.word (pointer + 1)),.val (.word (header - 247))] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atPointer,atLength,wordOpHOL,wordOp,valueIsWord,valueWord]
    obtain ⟨word,ready,final,_,tailRun,_⟩ := evaluate_rlpReadLength_decCall_normal entered output (ofString "n2")
      [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll2")] (.return (.op .add [.const 1,.var .local (ofString "ll2"),.var .local (ofString "n2")])) (pointer + 1) (header - 247) args code ticks bodyRun
    have terminal := evaluate_return_terminal (setVarHOLFinite (ofString "n2") (.val (.word word)) ready)
      (.op .add [.const 1,.var .local (ofString "ll2"),.var .local (ofString "n2")])
    rw [tailRun] at terminal
    exact terminal rfl

#print axioms evaluate_rlpUnchecked_long_list_terminal
end InitECandidate.Runtime
