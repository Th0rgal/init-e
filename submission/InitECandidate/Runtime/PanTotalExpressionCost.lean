import InitECandidate.Runtime.PanExpressionWork
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

mutual
  /-- Total source expression accounting, following exact evaluator guards.
  Memory rejection conservatively pays the requested word count; copying pays
  the actual output size. Operand lists retain every evaluator child. This is
  source work, not a claim that a unit already equals a native instruction. -/
  noncomputable def expressionEvents {F : Type} (s : PanSemStateFiniteExact 64 F)
      (e : ExpHOL 64) : List WorkEvent := by
    classical
    exact .expression :: (match e with
    | .const _ | .baseAddr | .topAddr | .bytesInWord => [.copy 1]
    | .var kind _ => .copy (resultWords s e) :: globalEvents kind (resultWords s e)
    | .rstruct fields => expressionListEvents s fields ++ [.copy (resultWords s e)]
    | .rfield _ value | .nfield _ value =>
        expressionEvents s value ++ [.copy (resultWords s e)]
    | .nstruct name fields =>
        match structContextLookupHOL name s.structs with
        | none => []
        | some info =>
            if info.fields.map Prod.fst = fields.map Prod.fst then
              expressionFieldEvents s fields ++ [.copy (resultWords s e)]
            else []
    | .load shape address =>
        if isWfShapeExactHOL s.structs shape then
          expressionEvents s address ++
            (if expressionIsWord s address then
              [.memory (sizeOfShapeWithContextHOL s.structs shape), .copy (resultWords s e)]
             else [])
        else []
    | .load32 address | .loadByte address =>
        expressionEvents s address ++
          (if expressionIsWord s address then [.memory 1, .copy (resultWords s e)] else [])
    | .op _ args | .panop _ args =>
        expressionListEvents s args ++ [.scalar args.length]
    | .cmp _ left right | .shift _ left right =>
        expressionEvents s left ++ expressionEvents s right ++
          (if expressionIsWord s left && expressionIsWord s right then [.scalar 1] else []))
  termination_by sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  noncomputable def expressionListEvents {F : Type} (s : PanSemStateFiniteExact 64 F) :
      List (ExpHOL 64) → List WorkEvent
    | [] => []
    | head :: tail => expressionEvents s head ++ expressionListEvents s tail
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  noncomputable def expressionFieldEvents {F : Type} (s : PanSemStateFiniteExact 64 F) :
      List (MlStringHOL × ExpHOL 64) → List WorkEvent
    | [] => []
    | (_, expression) :: tail => expressionEvents s expression ++ expressionFieldEvents s tail
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

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

/-- Every attempted expression is charged even if it fails before producing a value. -/
theorem expressionCost_entry {F : Type} (coeff : Work) (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) : coeff.expressions ≤ expressionCost coeff s e := by
  unfold expressionCost
  rw [expressionEvents.eq_def, executionWork_score_cons]
  simp only [WorkEvent.units, Work.score, Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero]
  omega

/-- A structured load pays for its evaluated address, requested memory words,
and actual returned words. Compiler-induced address replay remains a separate
lowering allowance rather than an extra source-expression occurrence. -/
theorem expressionCost_structured_load {F : Type} (coeff : Work)
    (s : PanSemStateFiniteExact 64 F) (shape : ShapeHOL) (address : ExpHOL 64)
    (wellFormed : isWfShapeExactHOL s.structs shape = true)
    (wordAddress : expressionIsWord s address = true) :
    expressionCost coeff s (.load shape address) =
      coeff.expressions + expressionCost coeff s address +
      coeff.memoryAccesses * sizeOfShapeWithContextHOL s.structs shape +
      coeff.movedWords * resultWords s (.load shape address) := by
  unfold expressionCost
  rw [expressionEvents]
  simp only [wellFormed, wordAddress, ↓reduceIte]
  rw [executionWork_score_cons, executionWork_score_append]
  simp [executionWork, WorkEvent.units, Work.score, Work.plus, Nat.add_assoc]

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

#print axioms expressionCost_entry
#print axioms expressionCost_structured_load
end InitECandidate.Runtime.FineCost
