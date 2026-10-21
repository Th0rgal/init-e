import InitECandidate.Runtime.PanSourcePriceDef
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

noncomputable def resultWords {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) : Nat :=
  ((expressionValue s e).map (fun value => (flattenHOL value).length)).getD 0

noncomputable def expressionIsWord {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) : Bool :=
  match expressionValue s e with
  | some (.val (.word _)) => true
  | _ => false

/-- Source expression accounting: one native-price event, the native Loop
price of the words `pan_to_crep` emits for the expression in this state
(`sourcePrice`). Every attempted expression is charged its price. -/
def expressionEvents {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) : List WorkEvent :=
  [.cost (sourcePrice s e)]

def expressionListEvents {F : Type} (s : PanSemStateFiniteExact 64 F) :
    List (ExpHOL 64) → List WorkEvent
  | [] => []
  | head :: tail => expressionEvents s head ++ expressionListEvents s tail

def expressionFieldEvents {F : Type} (s : PanSemStateFiniteExact 64 F) :
    List (MlStringHOL × ExpHOL 64) → List WorkEvent
  | [] => []
  | (_, expression) :: tail => expressionEvents s expression ++ expressionFieldEvents s tail

noncomputable def expressionCost {F : Type} (coeff : Work) (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) : Nat := coeff.score (executionWork (expressionEvents s e))

theorem executionWork_score_append (coeff : Work) (left right : List WorkEvent) :
    coeff.score (executionWork (left ++ right)) =
      coeff.score (executionWork left) + coeff.score (executionWork right) := by
  rw [executionWork_append, Work.score_plus]

theorem executionWork_score_cons (coeff : Work) (event : WorkEvent) (rest : List WorkEvent) :
    coeff.score (executionWork (event :: rest)) =
      coeff.score event.units + coeff.score (executionWork rest) := by
  simp only [executionWork, Work.score_plus]

/-- An expression costs its native price. -/
theorem expressionCost_eq {F : Type} (coeff : Work) (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) : expressionCost coeff s e = coeff.nativeCost * sourcePrice s e := by
  simp [expressionCost, expressionEvents, executionWork, WorkEvent.units, Work.plus, Work.score]

/-- Exact expression result paired with its canonical total work trace. -/
structure CostedExpressionRun {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (value : Option (ValueHOL 64)) (events : List WorkEvent) : Prop where
  sound : expressionValue s e = value
  events_eq : events = expressionEvents s e

/-- No successful-result or supported-syntax assumption is needed. -/
theorem costedExpressionRun_total {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) :
    CostedExpressionRun s e (expressionValue s e) (expressionEvents s e) := ⟨rfl, rfl⟩

#print axioms costedExpressionRun_total

#print axioms expressionCost_eq
end InitECandidate.Runtime.FineCost
