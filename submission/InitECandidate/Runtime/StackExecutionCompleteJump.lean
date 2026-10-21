import InitECandidate.Runtime.StackExecutionCompleteRaw
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

theorem executionComplete_jump {F : Type} (regX regY dest : Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (ih : ExecutionCompleteIH (.jumpLower regX regY dest) source) :
    ExecutionCompleteAt (.jumpLower regX regY dest) source := by
  intro result post run valid supported global scope
  have rootRun := run
  rw [StackSemEvaluate.evaluate_jumpLower] at run
  cases readX : StackSemStateOps.getVar regX source with
  | none =>
    simp only [readX] at run
    obtain ⟨rfl, _⟩ := Prod.mk.inj run
    exact False.elim valid
  | some x =>
    cases x with
    | loc _ _ =>
      simp only [readX] at run
      obtain ⟨rfl, _⟩ := Prod.mk.inj run
      exact False.elim valid
    | word x =>
      cases readY : StackSemStateOps.getVar regY source with
      | none =>
        simp only [readX, readY] at run
        obtain ⟨rfl, _⟩ := Prod.mk.inj run
        exact False.elim valid
      | some y =>
        cases y with
        | loc _ _ =>
          simp only [readX, readY] at run
          obtain ⟨rfl, _⟩ := Prod.mk.inj run
          exact False.elim valid
        | word y =>
          simp only [readX, readY] at run
          cases chosen : wordCmpHOL .lower x y with
          | false =>
            rw [chosen] at run
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
            exact ExecutionTrace.jumpFalse x y rootRun readX readY chosen
          | true =>
            rw [chosen] at run
            cases found : sptLookup dest source.code with
            | none =>
              simp only [StackSemControl.findCode, found] at run
              obtain ⟨rfl, _⟩ := Prod.mk.inj run
              exact False.elim valid
            | some prog =>
              simp only [StackSemControl.findCode, found] at run
              by_cases zero : source.clock = 0
              · rw [if_pos zero] at run
                obtain ⟨rfl, _⟩ := Prod.mk.inj run
                exact False.elim valid
              · rw [if_neg zero] at run
                rcases bodyRun : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock source) with ⟨bodyResult, middle⟩
                rw [bodyRun] at run
                dsimp only at run
                by_cases bad : StackSemControl.badFunReturn bodyResult = true
                · rw [if_pos bad] at run
                  obtain ⟨rfl, _⟩ := Prod.mk.inj run
                  exact False.elim valid
                · rw [if_neg bad] at run
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
                  have smaller : StackSemMeasure.LexNat
                      ((StackSemStateOps.decClock source).clock, sizeOf prog)
                      (source.clock, sizeOf (.jumpLower regX regY dest : HolProg 64)) := by
                    apply Prod.Lex.left
                    change source.clock - 1 < source.clock
                    omega
                  have tree := ih prog _ smaller bodyResult middle bodyRun valid
                    (global dest prog found) global (ExecutionLabelScope.of_lookup found)
                  have nonNormal : executionKindOfResult bodyResult ≠ .normal := by
                    cases bodyResult with
                    | none => exact False.elim (bad rfl)
                    | some value => exact executionKindOfResult_nonNormal value
                  exact ExecutionTrace.jumpTrue x y
                    (by simpa only [executionKindOfResult_result] using rootRun) zero readX readY chosen found nonNormal tree

#print axioms executionComplete_jump
end InitECandidate.Runtime.StackToLab
