import InitECandidate.Runtime.StackExecutionCompleteControl
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Validity transports backwards through loop exit, including label decrement. -/
theorem executionResultValid_of_exitLoop {code : Spt (HolProg 64)}
    {result : Option (StackSemResult 64)}
    (valid : ExecutionResultValid code (StackSemControl.exitLoop result)) :
    ExecutionResultValid code result := by
  cases result with
  | none => trivial
  | some value =>
    cases value <;> simp_all [StackSemControl.exitLoop, ExecutionResultValid]

/-- A stopped loop preserves terminal classification while decrementing control labels. -/
theorem executionTrace_loop_stopped {F : Type}
    {source post : StackSemStateFiniteExact 64 LabToTarget.Config F}
    {body : HolProg 64} {result : Option (StackSemResult 64)}
    (run : StackSemEvaluate.evaluate (.loop body, source) = (StackSemControl.exitLoop result, post))
    (tree : ExecutionTrace source body (executionKindOfResult result) post)
    (stopped : StackSemControl.contLoop result = false)
    (valid : ExecutionResultValid source.code result) :
    ExecutionTrace source (.loop body) (executionKindOfResult (StackSemControl.exitLoop result)) post := by
  cases result with
  | none => simp [StackSemControl.contLoop] at stopped
  | some result =>
    cases result with
    | error => exact False.elim valid
    | timeOut => exact False.elim valid
    | result value =>
      exact ExecutionTrace.loopExit run tree stopped rfl
    | exception value =>
      exact ExecutionTrace.loopExit run tree stopped rfl
    | halt value =>
      cases value with
      | loc _ _ => exact False.elim valid
      | word value => exact ExecutionTrace.loopFinal run tree stopped rfl
    | finalFFI event => exact ExecutionTrace.loopFinal run tree stopped rfl
    | «break» label =>
      by_cases zero : label = 0
      · subst label
        exact ExecutionTrace.loopBreak run tree
      · simpa only [StackSemControl.exitLoop, zero, ↓reduceIte, executionKindOfResult] using
          (ExecutionTrace.loopExit (by simpa only [StackSemControl.exitLoop, zero, ↓reduceIte] using run) tree stopped (by simp [StackSemControl.exitLoop, zero]))
    | «continue» label =>
      exact ExecutionTrace.loopExit run tree stopped rfl

/-- Reentry executes only after a positive remaining clock, so its
recursive completeness obligation strictly decreases the source clock. -/
theorem executionTrace_loop_reentry {F : Type}
    {source middle post : StackSemStateFiniteExact 64 LabToTarget.Config F}
    {body : HolProg 64} {bodyResult result : Option (StackSemResult 64)}
    (rootRun : StackSemEvaluate.evaluate (.loop body, source) = (result, post))
    (bodyRun : StackSemEvaluate.evaluate (body, source) = (bodyResult, middle))
    (bodyTree : ExecutionTrace source body (executionKindOfResult bodyResult) middle)
    (continues : StackSemControl.contLoop bodyResult = true)
    (positive : middle.clock ≠ 0)
    (rest : ExecutionTrace (StackSemStateOps.decClock middle) (.loop body)
      (executionKindOfResult result) post) :
    ExecutionTrace source (.loop body) (executionKindOfResult result) post := by
  have run : StackSemEvaluate.evaluate (.loop body, source) =
      ((executionKindOfResult result).result, post) := by
    simpa only [executionKindOfResult_result] using rootRun
  cases bodyResult with
  | none => exact ExecutionTrace.loopStep run bodyTree positive rest
  | some value =>
    cases value <;> simp only [StackSemControl.contLoop, Bool.false_eq_true] at continues
    rename_i label
    have zero : label = 0 := of_decide_eq_true continues
    subst label
    exact ExecutionTrace.loopContinue run bodyTree positive rest

theorem executionComplete_loop {F : Type} (body : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (ih : ExecutionCompleteIH (.loop body) source) :
    ExecutionCompleteAt (.loop body) source := by
  intro result post run valid supported global scope
  have rootRun := run
  rw [StackSemEvaluate.evaluate_loop, StackSemEvaluateClock.fixClockEvaluate] at run
  rcases bodyRun : StackSemEvaluate.evaluate (body, source) with ⟨bodyResult, middle⟩
  rw [bodyRun] at run
  dsimp only at run
  have bodySmaller : StackSemMeasure.LexNat (source.clock, sizeOf body)
      (source.clock, sizeOf (.loop body : HolProg 64)) := Prod.Lex.right _ (by simp)
  have bodySupported := executionSupported_loop.1 supported
  by_cases continues : StackSemControl.contLoop bodyResult = true
  · rw [if_pos continues] at run
    have bodyValid : ExecutionResultValid source.code bodyResult := by
      cases bodyResult with
      | none => trivial
      | some value =>
        cases value <;> simp only [StackSemControl.contLoop, Bool.false_eq_true] at continues
        trivial
    have bodyTree := ih body source bodySmaller bodyResult middle bodyRun bodyValid
      bodySupported global scope.loop_body
    by_cases zero : middle.clock = 0
    · rw [if_pos zero] at run
      have eq := (Prod.mk.inj run).1
      exact False.elim (valid.nontimeout eq.symm)
    · rw [if_neg zero] at run
      have clockLe := StackSemEvaluateClock.evaluateClock body source bodyResult middle bodyRun
      have restSmaller : StackSemMeasure.LexNat
          ((StackSemStateOps.decClock middle).clock, sizeOf (.loop body : HolProg 64))
          (source.clock, sizeOf (.loop body : HolProg 64)) := by
        apply Prod.Lex.left
        change middle.clock - 1 < source.clock
        omega
      have restValid : ExecutionResultValid (StackSemStateOps.decClock middle).code result := by
        change ExecutionResultValid middle.code result
        rw [bodyTree.code_eq]; exact valid
      have restGlobal : ExecutionCodeSupported (StackSemStateOps.decClock middle).code := by
        change ExecutionCodeSupported middle.code
        rw [bodyTree.code_eq]; exact global
      have restScope : ExecutionLabelScope (StackSemStateOps.decClock middle).code (.loop body) := by
        change ExecutionLabelScope middle.code (.loop body)
        rw [bodyTree.code_eq]; exact scope
      have restTree := ih (.loop body) _ restSmaller result post run restValid supported restGlobal restScope
      exact executionTrace_loop_reentry rootRun bodyRun bodyTree continues zero restTree
  · have stopped : StackSemControl.contLoop bodyResult = false := Bool.eq_false_iff.mpr continues
    rw [if_neg continues] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    have bodyValid := executionResultValid_of_exitLoop valid
    have bodyTree := ih body source bodySmaller bodyResult middle bodyRun bodyValid
      bodySupported global scope.loop_body
    exact executionTrace_loop_stopped rootRun bodyTree stopped bodyValid

#print axioms executionComplete_loop
#print axioms executionTrace_loop_reentry
#print axioms executionResultValid_of_exitLoop
#print axioms executionTrace_loop_stopped
end InitECandidate.Runtime.StackToLab
