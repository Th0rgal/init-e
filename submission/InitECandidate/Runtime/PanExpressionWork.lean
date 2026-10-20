import InitECandidate.Runtime.PanWorkVector
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

noncomputable def expressionValue {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) : Option (ValueHOL 64) :=
  @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e

/-- Initial exact expression rules. Variable copies use the flattened runtime
value size; expression entry is charged even when lookup fails. Recursive
expression constructors require explicit child rules and are not opaque leaves. -/
inductive ExpressionRun {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ExpHOL 64 → Option (ValueHOL 64) → List WorkEvent → Prop where
  | const (word : BitVec 64) :
      ExpressionRun s (.const word) (some (.val (.word word))) [.expression, .copy 1]
  | readVariable (kind : VarKind) (name) (value : ValueHOL 64)
      (lookup : expressionValue s (.var kind name) = some value) :
      ExpressionRun s (.var kind name) (some value)
        [.expression, .copy (flattenHOL value).length]
  | missingVariable (kind : VarKind) (name)
      (lookup : expressionValue s (.var kind name) = none) :
      ExpressionRun s (.var kind name) none [.expression]

theorem ExpressionRun.sound {F : Type} {s : PanSemStateFiniteExact 64 F}
    {e : ExpHOL 64} {value : Option (ValueHOL 64)} {events : List WorkEvent}
    (run : ExpressionRun s e value events) : expressionValue s e = value := by
  cases run with
  | const word => rfl
  | readVariable kind name value lookup => exact lookup
  | missingVariable kind name lookup => exact lookup

theorem variable_work_score (coeff : Work) (value : ValueHOL 64) :
    coeff.score (executionWork [.expression, .copy (flattenHOL value).length]) =
      coeff.expressions + coeff.movedWords * (flattenHOL value).length := by
  simp [executionWork, WorkEvent.units, Work.plus, Work.score]

#print axioms ExpressionRun.sound
#print axioms variable_work_score
end InitECandidate.Runtime.FineCost
