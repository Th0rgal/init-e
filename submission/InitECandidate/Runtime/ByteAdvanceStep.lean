import InitECandidate.Runtime.ByteStraightLine
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Byte-writing loop steps with scoped temporaries and one final counter advance. -/
inductive ByteAdvanceStep (counter : MlS) (increment : BitVec 64) : ProgHOL 64 → Prop
  | advance : ByteAdvanceStep counter increment
      (.assign .local counter (.op .add [.var .local counter,.const increment]))
  | store (destination value : ExpHOL 64) {rest : ProgHOL 64}
      (tail : ByteAdvanceStep counter increment rest) :
      ByteAdvanceStep counter increment (.seq (.storeByte destination value) rest)
  | declare (name : MlS) (initializer : ExpHOL 64) {body : ProgHOL 64}
      (different : name ≠ counter) (nested : ByteAdvanceStep counter increment body) :
      ByteAdvanceStep counter increment (.dec name .one initializer body)

/-- Even a failing byte operation is terminal. Normal completion advances the
counter exactly, and all other caller locals are preserved on every outcome. -/
theorem evaluate_byteAdvanceStep {F : Type} {counter : MlS} {increment : BitVec 64} {program : ProgHOL 64}
    (supported : ByteAdvanceStep counter increment program) (state : PanSemStateFiniteExact 64 F)
    (index : BitVec 64) (binding : state.locals.lookup counter = some (.val (.word index))) :
    ∃ result post, evaluateHOLFiniteState state program = (result,post) ∧ post.clock = state.clock ∧
      (∀ name, name ≠ counter → post.locals.lookup name = state.locals.lookup name) ∧
      ((result = none ∧ post.locals.lookup counter = some (.val (.word (index + increment)))) ∨ result = some .error) := by
  induction supported generalizing state with
  | advance =>
    refine ⟨none,setVarHOLFinite counter (.val (.word (index + increment))) state,?_,rfl,?_,Or.inl ⟨rfl,?_⟩⟩
    · simp [evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,binding,wordOpHOL,wordOp,valueIsWord,valueWord,lookupKvarHOLExact,isValidValueHOLExact,setKvarHOLFinite,shapeOfHOLExact,shapeEqHOL]
    · intro name different
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  | store destination value tail ih =>
    have facts := evaluate_storeByte_control_frame state destination value
    cases stored : evaluateHOLFiniteState state (.storeByte destination value) with
    | mk result middle =>
      rw [stored] at facts
      dsimp only at facts
      obtain ⟨control,clock,locals,_,_,_,_⟩ := facts
      rcases control with rfl | rfl
      · obtain ⟨result,post,run,postClock,frame,normal⟩ := ih middle (by rw [locals]; exact binding)
        refine ⟨result,post,?_,postClock.trans clock,?_,normal⟩
        · rw [evaluateHOLFiniteState_seq_line780,stored]; exact run
        · intro name different; rw [frame name different,locals]
      · refine ⟨some .error,middle,?_,clock,?_,Or.inr rfl⟩
        · rw [evaluateHOLFiniteState_seq_line780,stored]
        · intro name _; rw [locals]
  | declare name initializer different nested ih =>
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact ⟨some .error,state,rfl,rfl,(by intro _ _; rfl),Or.inr rfl⟩
    · rename_i value initialized
      split
      · have childBinding : (setVarHOLFinite name value state).locals.lookup counter = some (.val (.word index)) := by
          simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different] using binding
        obtain ⟨result,post,run,clock,frame,normal⟩ := ih (setVarHOLFinite name value state) childBinding
        rw [run]
        refine ⟨result,_,rfl,clock,?_,?_⟩
        · intro key other
          cases saved : state.locals.lookup name
          all_goals
            by_cases same : key = name
            · subst key; simp [saved,FDOMSUB_HOL,FUPDATE_HOL]
            · simp [FDOMSUB_HOL,FUPDATE_HOL,same,Ne.symm same,frame key other,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
        · rcases normal with ⟨rfl,advanced⟩ | rfl
          · left; refine ⟨rfl,?_⟩
            cases saved : state.locals.lookup name <;>
              simpa [lookup_resVarEq_toExact,resVarHOLExact,saved,FDOMSUB_HOL,FUPDATE_HOL,different,Ne.symm different] using advanced
          · exact Or.inr rfl
      · exact ⟨some .error,state,rfl,rfl,(by intro _ _; rfl),Or.inr rfl⟩

#print axioms evaluate_byteAdvanceStep
end InitECandidate.Runtime
