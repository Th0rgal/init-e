import InitECandidate.Runtime.PanStatementWork
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

def HasStatementCost {F : Type} (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64) : Prop :=
  ∃ result post events, StatementRun s p result post events

theorem StatementRun.hasCost {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {p : ProgHOL 64} {result events} (run : StatementRun s p result post events) :
    HasStatementCost s p := ⟨result, post, events, run⟩

/-- Every atomic source clause has a canonical expression/size-aware cost trace,
without assuming success, well-typed input, valid memory or an accepting oracle. -/
theorem atomic_statement_cost_complete {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p : ProgHOL 64) (supported : atomic p = true) : HasStatementCost s p := by
  classical
  cases p with
  | skip => exact (StatementRun.skip s).hasCost
  | assign kind name expression =>
    cases he : expressionValue s expression with
    | none => exact (StatementRun.assignFailure (kind := kind) (name := name) ⟨he, rfl⟩).hasCost
    | some value =>
      cases hv : isValidValueHOLFinite s kind name value with
      | true => exact (StatementRun.assignValue ⟨he, rfl⟩ hv).hasCost
      | false => exact (StatementRun.assignInvalid ⟨he, rfl⟩ hv).hasCost
  | primitive name operator arguments =>
    cases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments with
    | none => exact (StatementRun.primitiveArgumentsFailure (name := name) (operator := operator) ha).hasCost
    | some values =>
      cases hp : panPrimopHOLExact operator values with
      | none => exact (StatementRun.primitiveRejected (name := name) ha hp).hasCost
      | some value =>
        cases hv : isValidValueHOLFinite s .local name value with
        | true => exact (StatementRun.primitiveValue ha hp hv).hasCost
        | false => exact (StatementRun.primitiveInvalid ha hp hv).hasCost
  | store destination source =>
    by_cases word : ∃ address, expressionValue s destination = some (.val (.word address))
    · obtain ⟨address, hd⟩ := word
      cases hs : expressionValue s source with
      | none => exact (StatementRun.storeSourceFailure ⟨hd, rfl⟩ ⟨hs, rfl⟩).hasCost
      | some value =>
        cases hm : @panMemStoresHOL 64 _ address (flattenHOL value) s.memaddrs
            (fun a => Classical.propDecidable (s.memaddrs a)) s.memory with
        | none => exact (StatementRun.storeRejected ⟨hd, rfl⟩ ⟨hs, rfl⟩ hm).hasCost
        | some memory => exact (StatementRun.storeValue ⟨hd, rfl⟩ ⟨hs, rfl⟩ hm).hasCost
    · exact (StatementRun.storeInvalidAddress (source := source)
        (costedExpressionRun_total s destination) (fun address h => word ⟨address, h⟩)).hasCost
  | store32 destination source =>
    by_cases word : ∃ address, expressionValue s destination = some (.val (.word address))
    · obtain ⟨address, hd⟩ := word
      by_cases valueWord : ∃ value, expressionValue s source = some (.val (.word value))
      · obtain ⟨value, hs⟩ := valueWord
        cases hm : @panMemStore32HOL 64 _ s.memory s.memaddrs
            (fun a => Classical.propDecidable (s.memaddrs a)) s.be address
            (BitVec.ofNat 32 value.toNat) with
        | none => exact (StatementRun.store32Rejected ⟨hd, rfl⟩ ⟨hs, rfl⟩ hm).hasCost
        | some memory => exact (StatementRun.store32Value ⟨hd, rfl⟩ ⟨hs, rfl⟩ hm).hasCost
      · exact (StatementRun.store32InvalidValue ⟨hd, rfl⟩ (costedExpressionRun_total s source)
          (fun value h => valueWord ⟨value, h⟩)).hasCost
    · exact (StatementRun.store32InvalidAddress (source := source)
        (costedExpressionRun_total s destination) (fun address h => word ⟨address, h⟩)).hasCost
  | storeByte destination source =>
    by_cases word : ∃ address, expressionValue s destination = some (.val (.word address))
    · obtain ⟨address, hd⟩ := word
      by_cases valueWord : ∃ value, expressionValue s source = some (.val (.word value))
      · obtain ⟨value, hs⟩ := valueWord
        cases hm : @panMemStoreByteWord8HOL 64 _ s.memory s.memaddrs
            (fun a => Classical.propDecidable (s.memaddrs a)) s.be address
            (BitVec.ofNat 8 value.toNat) with
        | none => exact (StatementRun.storeByteRejected ⟨hd, rfl⟩ ⟨hs, rfl⟩ hm).hasCost
        | some memory => exact (StatementRun.storeByteValue ⟨hd, rfl⟩ ⟨hs, rfl⟩ hm).hasCost
      · exact (StatementRun.storeByteInvalidValue ⟨hd, rfl⟩ (costedExpressionRun_total s source)
          (fun value h => valueWord ⟨value, h⟩)).hasCost
    · exact (StatementRun.storeByteInvalidAddress (source := source)
        (costedExpressionRun_total s destination) (fun address h => word ⟨address, h⟩)).hasCost
  | «break» => exact (StatementRun.breakStmt s).hasCost
  | «continue» => exact (StatementRun.continueStmt s).hasCost
  | «return» expression =>
    cases he : expressionValue s expression with
    | none => exact (StatementRun.returnFailure ⟨he, rfl⟩).hasCost
    | some value =>
      by_cases size : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact value) ≤ 32
      · exact (StatementRun.returnValue ⟨he, rfl⟩ size).hasCost
      · exact (StatementRun.returnOversize ⟨he, rfl⟩ size).hasCost
  | raise exceptionId expression =>
    cases declared : s.eshapes.lookup exceptionId with
    | none => exact (StatementRun.raiseUndeclared (costedExpressionRun_total s expression) declared).hasCost
    | some shape =>
      cases he : expressionValue s expression with
      | none => exact (StatementRun.raiseFailure (exceptionId := exceptionId) ⟨he, rfl⟩).hasCost
      | some value =>
        by_cases valid : shapeOfHOLExact value = shape ∧
            sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact value) ≤ 32
        · exact (StatementRun.raiseValue ⟨he, rfl⟩ declared valid.1 valid.2).hasCost
        · exact (StatementRun.raiseRejectedValue ⟨he, rfl⟩ declared valid).hasCost
  | tick =>
    by_cases clock : s.clock = 0
    · exact (StatementRun.tickTimeout clock).hasCost
    · exact (StatementRun.tickStep clock).hasCost
  | annot tag text => exact (StatementRun.annotation (s := s) (tag := tag) (text := text)).hasCost
  | extCall function configuration configurationLength array arrayLength =>
    rcases he : evaluateHOLFiniteState s (.extCall function configuration configurationLength array arrayLength) with ⟨result, post⟩
    exact (StatementRun.external he).hasCost
  | shMemLoad operator kind name address =>
    rcases he : evaluateHOLFiniteState s (.shMemLoad operator kind name address) with ⟨result, post⟩
    exact (StatementRun.sharedLoad he).hasCost
  | shMemStore operator address value =>
    rcases he : evaluateHOLFiniteState s (.shMemStore operator address value) with ⟨result, post⟩
    exact (StatementRun.sharedStore he).hasCost
  | _ => simp [atomic] at supported

/-- The trace result is forced to agree with the authoritative evaluator. -/
theorem HasStatementCost.exact_trace {F : Type} {s : PanSemStateFiniteExact 64 F}
    {p : ProgHOL 64} (hasCost : HasStatementCost s p) :
    ∃ events, StatementRun s p (evaluateHOLFiniteState s p).1
      (evaluateHOLFiniteState s p).2 events := by
  obtain ⟨result, post, events, run⟩ := hasCost
  exact ⟨events, by simpa only [run.sound] using run⟩

theorem sequence_cost_complete {F : Type} (s : PanSemStateFiniteExact 64 F)
    (first second : ProgHOL 64) (one : HasStatementCost s first)
    (two : ∀ post, evaluateHOLFiniteState s first = (none, post) → HasStatementCost post second) :
    HasStatementCost s (.seq first second) := by
  obtain ⟨result, post, events, run⟩ := one
  cases result with
  | none =>
    obtain ⟨result2, post2, events2, run2⟩ := two post run.sound
    exact (StatementRun.seqNext run run2).hasCost
  | some result => exact (StatementRun.seqStop (second := second) (by simp) run).hasCost

theorem conditional_cost_complete {F : Type} (s : PanSemStateFiniteExact 64 F)
    (condition : ExpHOL 64) (yes no : ProgHOL 64)
    (branch : ∀ word, expressionValue s condition = some (.val (.word word)) →
      HasStatementCost s (if word = 0 then no else yes)) :
    HasStatementCost s (.ite condition yes no) := by
  classical
  by_cases word : ∃ value, expressionValue s condition = some (.val (.word value))
  · obtain ⟨value, guard⟩ := word
    have chosen := branch value guard
    by_cases zero : value = 0
    · simp only [zero, ↓reduceIte] at chosen
      obtain ⟨result, post, events, run⟩ := chosen
      subst value
      exact (StatementRun.iteNo (yes := yes) ⟨guard, rfl⟩ run).hasCost
    · simp only [zero, ↓reduceIte] at chosen
      obtain ⟨result, post, events, run⟩ := chosen
      exact (StatementRun.iteYes (no := no) ⟨guard, rfl⟩ zero run).hasCost
  · exact (StatementRun.iteInvalidGuard (yes := yes) (no := no)
      (costedExpressionRun_total s condition) (fun value h => word ⟨value, h⟩)).hasCost

theorem declaration_cost_complete {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlStringHOL) (shape : ShapeHOL) (initializer : ExpHOL 64) (body : ProgHOL 64)
    (bodyCost : ∀ value, expressionValue s initializer = some value →
      shapeEqHOL shape (shapeOfHOLExact value) = true →
      HasStatementCost (setVarHOLFinite name value s) body) :
    HasStatementCost s (.dec name shape initializer body) := by
  cases he : expressionValue s initializer with
  | none => exact (StatementRun.declareFailure (name := name) (shape := shape) (body := body) ⟨he, rfl⟩).hasCost
  | some value =>
    cases matchesShape : shapeEqHOL shape (shapeOfHOLExact value) with
    | false => exact (StatementRun.declareMismatch (name := name) (body := body) ⟨he, rfl⟩ matchesShape).hasCost
    | true =>
      obtain ⟨result, post, events, run⟩ := bodyCost value he matchesShape
      exact (StatementRun.declareValue ⟨he, rfl⟩ matchesShape run).hasCost

#print axioms sequence_cost_complete
#print axioms conditional_cost_complete
#print axioms declaration_cost_complete

/-- Loop completeness follows the actual body result and recurses only on
normal/continue exits. The global proof must discharge these recursive costs. -/
theorem while_cost_complete {F : Type} (s : PanSemStateFiniteExact 64 F)
    (condition : ExpHOL 64) (body : ProgHOL 64)
    (bodyCost : ∀ word, expressionValue s condition = some (.val (.word word)) →
      word ≠ 0 → s.clock ≠ 0 → HasStatementCost (decClockHOLFinite s) body)
    (nextCost : s.clock ≠ 0 → ∀ post, evaluateHOLFiniteState (decClockHOLFinite s) body = (none, post) →
      HasStatementCost post (.while condition body))
    (continueCost : s.clock ≠ 0 → ∀ post,
      evaluateHOLFiniteState (decClockHOLFinite s) body = (some .continue, post) →
      HasStatementCost post (.while condition body)) :
    HasStatementCost s (.while condition body) := by
  classical
  by_cases word : ∃ value, expressionValue s condition = some (.val (.word value))
  · obtain ⟨value, guard⟩ := word
    by_cases zero : value = 0
    · subst value
      exact (StatementRun.whileFalse (body := body) ⟨guard, rfl⟩).hasCost
    · by_cases clock : s.clock = 0
      · exact (StatementRun.whileTimeout (body := body) ⟨guard, rfl⟩ zero clock).hasCost
      · obtain ⟨result, post, events, run⟩ := bodyCost value guard zero clock
        cases result with
        | none =>
          obtain ⟨result2, post2, events2, run2⟩ := nextCost clock post run.sound
          exact (StatementRun.whileNext ⟨guard, rfl⟩ zero clock run run2).hasCost
        | some result =>
          cases result with
          | «break» => exact (StatementRun.whileBreak ⟨guard, rfl⟩ zero clock run).hasCost
          | «continue» =>
            obtain ⟨result2, post2, events2, run2⟩ := continueCost clock post run.sound
            exact (StatementRun.whileContinue ⟨guard, rfl⟩ zero clock run run2).hasCost
          | _ => exact (StatementRun.whilePropagate ⟨guard, rfl⟩ zero clock
              (by intro h; cases h) (by intro h; cases h) run).hasCost
  · exact (StatementRun.whileInvalidGuard (body := body) (costedExpressionRun_total s condition)
      (fun value h => word ⟨value, h⟩)).hasCost

#print axioms while_cost_complete

#print axioms atomic_statement_cost_complete
#print axioms HasStatementCost.exact_trace
end InitECandidate.Runtime.FineCost
