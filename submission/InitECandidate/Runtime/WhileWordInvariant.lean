import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A loop whose body either continues normally or fails can retain a
watched word on every outcome, without a successful-access or fuel premise. -/
theorem evaluate_while_word_invariant {F : Type}
    (condition : ExpHOL 64) (body : ProgHOL 64)
    (invariant : PanSemStateFiniteExact 64 F → Prop) (watched : BitVec 64)
    (guard : ∀ state, invariant state → ∃ flag : BitVec 64,
      evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) condition =
        some (.val (.word flag)))
    (step : ∀ state, invariant state → ∀ flag : BitVec 64,
      evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) condition =
        some (.val (.word flag)) → flag ≠ 0 →
      ∃ result post,
        evaluateHOLFiniteState (decClockHOLFinite state) body = (result,post) ∧
        post.clock = state.clock - 1 ∧ post.memory watched = state.memory watched ∧
        ((result = none ∧ invariant post) ∨ result = some .error))
    (state : PanSemStateFiniteExact 64 F) (valid : invariant state) :
    (evaluateHOLFiniteState state (.while condition body)).2.memory watched = state.memory watched ∧
      ((evaluateHOLFiniteState state (.while condition body)).1 = none →
        invariant (evaluateHOLFiniteState state (.while condition body)).2) := by
  obtain ⟨flag,conditionRun⟩ := guard state valid
  rw [evaluateHOLFiniteState_while_total,conditionRun]
  dsimp only
  by_cases active : flag ≠ 0
  · rw [if_pos active]
    by_cases empty : state.clock = 0
    · rw [if_pos empty]
      exact ⟨rfl,by intro impossible; cases impossible⟩
    · rw [if_neg empty]
      obtain ⟨result,post,bodyRun,clock,frame,outcome⟩ := step state valid flag conditionRun active
      rw [bodyRun]
      dsimp only
      have fixed : ¬(decClockHOLFinite state).clock < post.clock := by
        change ¬state.clock - 1 < post.clock
        omega
      rcases outcome with ⟨rfl,postValid⟩ | rfl
      · have smaller : post.clock < state.clock := by omega
        obtain ⟨tailFrame,tailValid⟩ := evaluate_while_word_invariant condition body invariant watched
          guard step post postValid
        simpa only [fixClockHOLFinite,if_neg fixed] using
          (show (evaluateHOLFiniteState post (.while condition body)).2.memory watched = state.memory watched ∧
            ((evaluateHOLFiniteState post (.while condition body)).1 = none →
              invariant (evaluateHOLFiniteState post (.while condition body)).2) from
            ⟨tailFrame.trans frame,tailValid⟩)
      · simp only [fixClockHOLFinite,if_neg fixed]
        exact ⟨frame,by intro impossible; cases impossible⟩
  · rw [if_neg active]
    exact ⟨rfl,fun _ => valid⟩
termination_by state.clock

end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.evaluate_while_word_invariant
