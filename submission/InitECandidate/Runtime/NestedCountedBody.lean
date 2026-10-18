import InitECandidate.Runtime.CountedLoop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Counted bodies may declare temporary locals around the increment, as the
original SHA block loops do. Those declarations must not shadow the counter. -/
inductive NestedCountedBody (counter : MlS) (step : BitVec 64) : ProgHOL 64 → Nat → Prop
  | base {body : ProgHOL 64} {cost : Nat} (counted : CountedBody counter step body cost) :
      NestedCountedBody counter step body cost
  | dec (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64)
      {body : ProgHOL 64} {cost : Nat} (different : name ≠ counter)
      (inner : NestedCountedBody counter step body cost) :
      NestedCountedBody counter step (.dec name shape initializer body) cost

theorem NestedCountedBody.run {counter : MlS} {step : BitVec 64}
    {body : ProgHOL 64} {cost : Nat} (counted : NestedCountedBody counter step body cost)
    {F : Type} (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode)
    (w : BitVec 64) (atCounter : state.locals.lookup counter = some (.val (.word w)))
    (budget : cost ≤ state.clock) :
    state.clock ≤ (evaluateHOLFiniteState state body).2.clock + cost ∧
      (evaluateHOLFiniteState state body).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state body).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState state body).1 ≠ some .continue ∧
      ((evaluateHOLFiniteState state body).1 = none →
        (evaluateHOLFiniteState state body).2.locals.lookup counter = some (.val (.word (w + step))) ∧
        (evaluateHOLFiniteState state body).2.code = state.code) := by
  induction counted generalizing state with
  | base inner => exact inner.run state code w atCounter budget
  | dec name shape initializer different inner ih =>
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    cases initialized : @evalHOLExact 64 F _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a)) initializer with
    | none => simp
    | some value =>
      dsimp only
      split
      · have atEntered : (setVarHOLFinite name value state).locals.lookup counter = some (.val (.word w)) := by
          simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different] using atCounter
        have bounded := ih (setVarHOLFinite name value state) code atEntered budget
        cases bodyRun : evaluateHOLFiniteState (setVarHOLFinite name value state) _ with
        | mk result post =>
          rw [bodyRun] at bounded
          dsimp only at bounded ⊢
          obtain ⟨spent,kept,safe,noContinue,advance⟩ := bounded
          refine ⟨spent,kept,safe,noContinue,?_⟩
          intro normal
          obtain ⟨nextCounter,nextCode⟩ := advance normal
          refine ⟨?_,nextCode⟩
          rw [resVarEq_lookup,if_neg (Ne.symm different)]
          exact nextCounter
      · simp

#print axioms NestedCountedBody.run
end InitECandidate.Runtime
