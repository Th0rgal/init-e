import InitECandidate.Runtime.ByteAdvanceStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Read-only equality checks can return false early before advancing a counter. -/
inductive ReadCheckAdvanceStep (counter : MlS) (increment : BitVec 64) : ProgHOL 64 → Prop
  | advance : ReadCheckAdvanceStep counter increment
      (.assign .local counter (.op .add [.var .local counter,.const increment]))
  | check (condition : ExpHOL 64) {rest : ProgHOL 64}
      (tail : ReadCheckAdvanceStep counter increment rest) :
      ReadCheckAdvanceStep counter increment (.seq (.ite condition (.return (.const 0)) .skip) rest)

/-- Normal comparison steps advance their counter and preserve other locals.
A failed load or an unequal comparison exits without timeout or loop control. -/
theorem evaluate_readCheckAdvanceStep {F : Type} {counter : MlS} {increment : BitVec 64} {program : ProgHOL 64}
    (supported : ReadCheckAdvanceStep counter increment program) (state : PanSemStateFiniteExact 64 F)
    (index : BitVec 64) (binding : state.locals.lookup counter = some (.val (.word index))) :
    ∃ result post, evaluateHOLFiniteState state program = (result,post) ∧ post.clock = state.clock ∧
      ((result = none ∧ post.locals.lookup counter = some (.val (.word (index + increment))) ∧
        (∀ name, name ≠ counter → post.locals.lookup name = state.locals.lookup name)) ∨
       result = some .error ∨ result = some (.returned (.val (.word (0 : BitVec 64))))) := by
  induction supported generalizing state with
  | advance =>
    obtain ⟨result,post,run,clock,frame,normal⟩ := evaluate_byteAdvanceStep ByteAdvanceStep.advance state index binding
    refine ⟨result,post,run,clock,?_⟩
    rcases normal with ⟨rfl,advanced⟩ | rfl
    · exact Or.inl ⟨rfl,advanced,frame⟩
    · exact Or.inr (Or.inl rfl)
  | check condition tail ih =>
    rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
    split
    · split
      · simp only [evaluateHOLFiniteState_skip]
        exact ih state binding
      · simp only [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
        exact ⟨_,_,rfl,rfl,Or.inr (Or.inr rfl)⟩
    · exact ⟨some .error,state,rfl,rfl,Or.inr (Or.inl rfl)⟩

#print axioms evaluate_readCheckAdvanceStep
end InitECandidate.Runtime
