import InitECandidate.Runtime.RlpReadLengthLoopAgreement
import InitECandidate.Runtime.NoDirectReturn
import InitECandidate.Runtime.PanWhileNoReturn
import InitECandidate.Runtime.PanDecWordResultScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual byte-reader loop cannot bypass its final return. -/
theorem evaluate_rlpReadLength_loop_no_return {F : Type} (state : PanSemStateFiniteExact 64 F) (value : ValueHOL 64) :
    (evaluateHOLFiniteState state rlpReadLengthLoop).1 ≠ some (.returned value) := by
  rw [source_rlpReadLength_loop]
  apply evaluate_while_no_return
  intro current result
  apply evaluate_noDirectReturn
  rw [source_rlpReadLength_step]
  rfl

/-- A returned loop/return sequence proves normal loop completion and exposes
its actual accumulator binding as the returned value. -/
theorem rlpReadLength_return_exposes_loop {F : Type} (state post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (.seq rlpReadLengthLoop (.return (.var .local (ofString "v")))) =
      (some (.returned value),post)) :
    ∃ loopPost, evaluateHOLFiniteState state rlpReadLengthLoop = (none,loopPost) ∧
      loopPost.locals.lookup (ofString "v") = some value := by
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases loop : evaluateHOLFiniteState state rlpReadLengthLoop with
  | mk result loopPost =>
    rw [loop] at run
    cases result with
    | some result =>
      have impossible := evaluate_rlpReadLength_loop_no_return state value
      rw [loop] at impossible
      exact False.elim (impossible (Prod.mk.inj run).1)
    | none =>
      dsimp only at run
      rw [evaluateHOLFiniteState_return] at run
      cases binding : loopPost.locals.lookup (ofString "v") with
      | none => simp [evalHOLExact,binding] at run
      | some actual =>
        simp only [evalHOLExact,binding] at run
        split at run
        · have equal := PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj run).1)
          exact ⟨loopPost,rfl,by rw [binding,equal]⟩
        · cases run

/-- Actual initialization shadows the accumulator/index before the loop. -/
def rlpReadLengthInitialState {F : Type} (state : PanSemStateFiniteExact 64 F) : PanSemStateFiniteExact 64 F :=
  setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64)))
    (setVarHOLFinite (ofString "v") (.val (.word (0 : BitVec 64))) state)

theorem rlpReadLength_after_check_returned_loop {F : Type} (state post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state rlpReadLengthAfterCheck = (some (.returned value),post)) :
    ∃ loopPost, evaluateHOLFiniteState (rlpReadLengthInitialState state) rlpReadLengthLoop = (none,loopPost) ∧
      loopPost.locals.lookup (ofString "v") = some value := by
  rw [source_rlpReadLength_after_check] at run
  obtain ⟨middle,bodyRun,_⟩ := evaluate_dec_word_result_scope state post (ofString "v") (.const 0) 0 _
    (some (.returned value)) (by rfl) run
  obtain ⟨output,tail,_⟩ := evaluate_dec_word_result_scope
    (setVarHOLFinite (ofString "v") (.val (.word (0 : BitVec 64))) state) middle (ofString "i") (.const 0) 0 _
    (some (.returned value)) (by rfl) bodyRun
  exact rlpReadLength_return_exposes_loop (rlpReadLengthInitialState state) output value tail

#print axioms evaluate_rlpReadLength_loop_no_return
#print axioms rlpReadLength_after_check_returned_loop
end InitECandidate.Runtime
