import InitECandidate.Runtime.RlpItemLongBodyBound
import InitECandidate.Runtime.RlpItemLongTerminal
import InitECandidate.Runtime.PanDecWordResultScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_rlpItem_long_body_terminal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer headerLength : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (code : state.code = originalRuntimeCode) (ticks : headerLength.toNat + 3 ≤ state.clock) :
    (evaluateHOLFiniteState state rlpItemLongBody).1 ≠ none := by
  obtain ⟨result,post,run,_,_,_,normal,_,_,_⟩ := evaluate_rlp_error_check state
    (.cmp .lower (.op .sub [.var .local (ofString "len"),.const 1]) (.var .local (ofString "ll"))) 3 code (by omega)
  rw [source_rlpItem_long_body,evaluateHOLFiniteState_seq_line780,run]
  cases result with
  | none =>
    have same := normal rfl
    subst post
    exact evaluate_rlpItem_long_read_terminal state pointer headerLength pointerLocal headerLocal code (by omega)
  | some stopped => simp

/-- Neither failure nor successful parsing falls through the original long
string declaration, so later RLP list branches cannot execute. -/
theorem evaluate_rlpItem_long_string_terminal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (lower : 183 < header.toNat) (upper : header.toNat ≤ 191)
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock) :
    (evaluateHOLFiniteState state rlpItemLongString).1 ≠ none := by
  intro normal
  cases run : evaluateHOLFiniteState state rlpItemLongString with
  | mk result post =>
    rw [run] at normal
    change result = none at normal
    subst result
    have initializer : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.op .sub [.var .local (ofString "b"),.const 183]) = some (.val (.word (header - 183))) := by
      simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    rw [source_rlpItem_long_string] at run
    obtain ⟨output,bodyRun,_⟩ := evaluate_dec_word_result_scope state post (ofString "ll")
      (.op .sub [.var .local (ofString "b"),.const 183]) (header - 183) rlpItemLongBody none initializer run
    let entered := setVarHOLFinite (ofString "ll") (.val (.word (header - 183))) state
    have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
      simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "ll" ≠ ofString "p" by decide] using pointerLocal
    have atLength : entered.locals.lookup (ofString "ll") = some (.val (.word (header - 183))) := by
      simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have sizeBound := (rlp_long_string_length_bytes header lower upper).2
    have terminal := evaluate_rlpItem_long_body_terminal entered pointer (header - 183) atPointer atLength code
      (by change (header - 183).toNat + 3 ≤ state.clock; omega)
    rw [bodyRun] at terminal
    exact terminal rfl

#print axioms evaluate_rlpItem_long_body_terminal
#print axioms evaluate_rlpItem_long_string_terminal
end InitECandidate.Runtime
