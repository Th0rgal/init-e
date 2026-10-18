import InitECandidate.Runtime.OutputWriteSource
import InitECandidate.Runtime.SharedStoreControlFrame
import InitECandidate.Runtime.ByteAdvanceStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- One actual output-write iteration either advances i or terminates at
an invalid access/host event, preserving every other local and the clock. -/
theorem evaluate_outputWrite_step {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index : BitVec 64) (binding : state.locals.lookup (ofString "i") = some (.val (.word index))) :
    ∃ result post, evaluateHOLFiniteState state outputWriteStep = (result,post) ∧ post.clock = state.clock ∧
      (∀ key, key ≠ ofString "i" → post.locals.lookup key = state.locals.lookup key) ∧
      ((result = none ∧ post.locals.lookup (ofString "i") = some (.val (.word (index + 1)))) ∨
        result = some .error ∨ ∃ event, result = some (.finalFfi event)) := by
  have facts := evaluate_shared_store_control_frame state .op8
    (.op .add [.const 2688614400,.var .local (ofString "i")])
    (.loadByte (.op .add [.var .local (ofString "src"),.var .local (ofString "i")]))
  change ((evaluateHOLFiniteState state outputWriteStore).1 = none ∨
    (evaluateHOLFiniteState state outputWriteStore).1 = some .error ∨
    ∃ event, (evaluateHOLFiniteState state outputWriteStore).1 = some (.finalFfi event)) ∧
    (evaluateHOLFiniteState state outputWriteStore).2.clock = state.clock ∧
    (∀ key, (evaluateHOLFiniteState state outputWriteStore).2.locals.lookup key = state.locals.lookup key) at facts
  cases stored : evaluateHOLFiniteState state outputWriteStore with
  | mk result middle =>
    rw [stored] at facts
    obtain ⟨control,clock,locals⟩ := facts
    rcases control with rfl | rfl | ⟨event,rfl⟩
    · obtain ⟨result,post,run,ticks,frame,normal⟩ := evaluate_byteAdvanceStep
        (ByteAdvanceStep.advance (counter := ofString "i") (increment := (1 : BitVec 64))) middle index
        ((locals _).trans binding)
      refine ⟨result,post,?_,ticks.trans clock,?_,?_⟩
      · rw [outputWriteStep,evaluateHOLFiniteState_seq_line780,stored]; exact run
      · intro key different
        exact (frame key different).trans (locals key)
      · rcases normal with normal | error
        · exact Or.inl normal
        · exact Or.inr (Or.inl error)
    · refine ⟨some .error,middle,?_,clock,(fun key _ => locals key),Or.inr (Or.inl rfl)⟩
      rw [outputWriteStep,evaluateHOLFiniteState_seq_line780,stored]
    · refine ⟨some (.finalFfi event),middle,?_,clock,(fun key _ => locals key),Or.inr (Or.inr ⟨event,rfl⟩)⟩
      rw [outputWriteStep,evaluateHOLFiniteState_seq_line780,stored]

#print axioms evaluate_outputWrite_step
end InitECandidate.Runtime
