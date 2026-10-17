import InitECandidate.Runtime.RlpHeaderLongStringReadBound
import InitECandidate.Runtime.PanSequenceTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The validation block ends in an original return and cannot fall through,
even at zero clock or with arbitrary code and malformed local values. -/
theorem evaluate_rlpHeader_long_string_finish_terminal {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state rlpHeaderLongStringFinish).1 ≠ none := by
  rw [source_rlpHeader_long_string_finish]
  change (evaluateHOLFiniteState state (.seq _ (.seq _ rlpHeaderLongStringReturn))).1 ≠ none
  apply evaluate_seq_terminal
  intro middle
  apply evaluate_seq_terminal
  intro final
  exact evaluate_return_terminal final _

/-- A normally completed length-reader declaration would have to fall
through the terminal long-string header finish, so the original read cannot fall through. -/
theorem evaluate_rlpHeader_long_string_read_terminal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer headerLength : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (code : state.code = originalRuntimeCode) (ticks : headerLength.toNat + 2 ≤ state.clock) :
    (evaluateHOLFiniteState state rlpHeaderLongStringRead).1 ≠ none := by
  intro normal
  cases run : evaluateHOLFiniteState state rlpHeaderLongStringRead with
  | mk result post =>
    rw [run] at normal
    change result = none at normal
    subst result
    rw [source_rlpHeader_long_string_read] at run
    have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll")] =
        some [.val (.word (pointer + 1)),.val (.word headerLength)] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    obtain ⟨word,ready,output,_,tail,_⟩ := evaluate_rlpReadLength_decCall_normal state post (ofString "n")
      [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "ll")]
      rlpHeaderLongStringFinish (pointer + 1) headerLength args code ticks run
    have terminal := evaluate_rlpHeader_long_string_finish_terminal (setVarHOLFinite (ofString "n") (.val (.word word)) ready)
    rw [tail] at terminal
    exact terminal rfl

#print axioms evaluate_rlpHeader_long_string_finish_terminal
#print axioms evaluate_rlpHeader_long_string_read_terminal
end InitECandidate.Runtime
