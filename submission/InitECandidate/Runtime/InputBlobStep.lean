import InitECandidate.Runtime.InputBlobSource
import InitECandidate.Runtime.SharedLoadControlFrame
import InitECandidate.Runtime.WordAdvanceStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original input copy step reads a shared word, writes it, then
advances by eight. Failed accesses and host termination consume no ticks. -/
theorem evaluate_inputBlob_step {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index : BitVec 64) (atIndex : state.locals.lookup (ofString "i") = some (.val (.word index))) :
    ∃ result post, evaluateHOLFiniteState state inputBlobStep = (result,post) ∧ post.clock = state.clock ∧
      (result = none → ∀ key, key ≠ ofString "i" → key ≠ ofString "w" → post.locals.lookup key = state.locals.lookup key) ∧
      ((result = none ∧ post.locals.lookup (ofString "i") = some (.val (.word (index + 8)))) ∨
        result = some .error ∨ ∃ event, result = some (.finalFfi event)) := by
  have facts := evaluate_shared_load_control_frame state .opW (ofString "w")
    (.op .add [.const 1073741840,.var .local (ofString "i")])
  change (evaluateHOLFiniteState state inputBlobLoad).2.clock = state.clock ∧
    ((evaluateHOLFiniteState state inputBlobLoad).1 = none ∨
      (evaluateHOLFiniteState state inputBlobLoad).1 = some .error ∨
      ∃ event, (evaluateHOLFiniteState state inputBlobLoad).1 = some (.finalFfi event)) ∧
    (evaluateHOLFiniteState state inputBlobLoad).2.globals = state.globals ∧
    (evaluateHOLFiniteState state inputBlobLoad).2.memory = state.memory ∧
    (evaluateHOLFiniteState state inputBlobLoad).2.memaddrs = state.memaddrs ∧
    ((evaluateHOLFiniteState state inputBlobLoad).1 = none → ∃ word : BitVec 64,
      (evaluateHOLFiniteState state inputBlobLoad).2.locals.lookup (ofString "w") = some (.val (.word word)) ∧
      ∀ key, key ≠ ofString "w" →
        (evaluateHOLFiniteState state inputBlobLoad).2.locals.lookup key = state.locals.lookup key) at facts
  cases loaded : evaluateHOLFiniteState state inputBlobLoad with
  | mk result middle =>
    rw [loaded] at facts
    obtain ⟨clock,control,_,_,_,normal⟩ := facts
    rcases control with rfl | rfl | ⟨event,rfl⟩
    · obtain ⟨word,_,locals⟩ := normal rfl
      obtain ⟨result,post,run,ticks,frame,normal⟩ := evaluate_wordAdvanceStep
        (WordAdvanceStep.store (.op .add [.var .local (ofString "p"),.var .local (ofString "i")])
          (.var .local (ofString "w")) (WordAdvanceStep.advance (counter := ofString "i") (increment := (8 : BitVec 64))))
        middle index ((locals _ (by decide)).trans atIndex)
      refine ⟨result,post,?_,ticks.trans clock,?_,?_⟩
      · rw [inputBlobStep,evaluateHOLFiniteState_seq_line780,loaded]; exact run
      · intro _ key notIndex notWord
        exact (frame key notIndex).trans (locals key notWord)
      · rcases normal with advanced | error
        · exact Or.inl advanced
        · exact Or.inr (Or.inl error)
    · refine ⟨some .error,middle,?_,clock,?_,Or.inr (Or.inl rfl)⟩
      · rw [inputBlobStep,evaluateHOLFiniteState_seq_line780,loaded]
      · intro impossible; cases impossible
    · refine ⟨some (.finalFfi event),middle,?_,clock,?_,Or.inr (Or.inr ⟨event,rfl⟩)⟩
      · rw [inputBlobStep,evaluateHOLFiniteState_seq_line780,loaded]
      · intro impossible; cases impossible

#print axioms evaluate_inputBlob_step
end InitECandidate.Runtime
