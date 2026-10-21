import InitECandidate.Runtime.StackExecutionCompleteTail
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

theorem executionComplete_raw {F : Type} (dest : Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (ih : ExecutionCompleteIH (.rawCall dest) source) :
    ExecutionCompleteAt (.rawCall dest) source := by
  intro result post run valid supported global scope
  have rootRun := run
  rw [StackSemEvaluate.evaluate_rawCall] at run
  cases found : sptLookup dest source.code with
  | none =>
    simp only [found] at run
    obtain ⟨rfl, _⟩ := Prod.mk.inj run
    exact False.elim valid
  | some stored =>
    rw [found] at run
    cases stored <;> simp only [StackSemControl.destSeq] at run
    all_goals try (obtain ⟨rfl, _⟩ := Prod.mk.inj run; exact False.elim valid)
    rename_i prologue prog
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
            (source.clock, sizeOf (.rawCall dest : HolProg 64)) := by
          apply Prod.Lex.left
          change source.clock - 1 < source.clock
          omega
        have tree := ih prog _ smaller bodyResult middle bodyRun valid
          (executionSupported_seq.1 (global dest _ found)).2 global
          (ExecutionLabelScope.of_lookup found).seq_right
        have nonNormal : executionKindOfResult bodyResult ≠ .normal := by
          cases bodyResult with
          | none => exact False.elim (bad rfl)
          | some value => exact executionKindOfResult_nonNormal value
        exact ExecutionTrace.rawCall
          (by simpa only [executionKindOfResult_result] using rootRun) zero found nonNormal tree

#print axioms executionComplete_raw
end InitECandidate.Runtime.StackToLab
