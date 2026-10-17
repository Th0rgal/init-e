import InitECandidate.Runtime.RlpUncheckedSource
import InitECandidate.Runtime.RlpReadLengthDeclarationFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_rlpUnchecked_long_string_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (code : state.code = originalRuntimeCode) :
    let evaluated := evaluateHOLFiniteState state rlpUncheckedLongString
    evaluated.2.memory = state.memory ∧ evaluated.2.globals = state.globals := by
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
  have bound := evaluate_rlpReadLength_declaration_frame entered (ofString "n")
    (.return (.op .add [.const 1,.var .local (ofString "ll"),.var .local (ofString "n")])) (by decide)
    [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll")]
    (pointer + 1) (header - 183) args code
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 183]) = some (.val (.word (header - 183))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpUnchecked_long_string,evaluateHOLFiniteState_dec_total]
  simp only [initializer,shapeOfHOLExact,shapeEqHOL,if_true]
  cases run : evaluateHOLFiniteState entered (.decCall (ofString "n") .one (ofString "rlp_read_length")
      [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll")]
      (.return (.op .add [.const 1,.var .local (ofString "ll"),.var .local (ofString "n")]))) with
  | mk result post =>
    rw [run] at bound
    exact bound


#print axioms evaluate_rlpUnchecked_long_string_frame

theorem evaluate_rlpUnchecked_long_list_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (code : state.code = originalRuntimeCode) :
    let evaluated := evaluateHOLFiniteState state rlpUncheckedLongList
    evaluated.2.memory = state.memory ∧ evaluated.2.globals = state.globals := by
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
  have bound := evaluate_rlpReadLength_declaration_frame entered (ofString "n2")
    (.return (.op .add [.const 1,.var .local (ofString "ll2"),.var .local (ofString "n2")])) (by decide)
    [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll2")]
    (pointer + 1) (header - 247) args code
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 247]) = some (.val (.word (header - 247))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpUnchecked_long_list,evaluateHOLFiniteState_dec_total]
  simp only [initializer,shapeOfHOLExact,shapeEqHOL,if_true]
  cases run : evaluateHOLFiniteState entered (.decCall (ofString "n2") .one (ofString "rlp_read_length")
      [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll2")]
      (.return (.op .add [.const 1,.var .local (ofString "ll2"),.var .local (ofString "n2")]))) with
  | mk result post =>
    rw [run] at bound
    exact bound


#print axioms evaluate_rlpUnchecked_long_list_frame

end InitECandidate.Runtime
