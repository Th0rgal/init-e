import InitECandidate.Runtime.StackExecutionCompleteLoop
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Successful dynamic lookup always identifies an installed code entry. -/
theorem execution_findCode_lookup {dest : Sum Nat Nat}
    {regs : HolFiniteMapExact Nat (WordLocW 64)} {code : Spt (HolProg 64)} {prog : HolProg 64}
    (found : StackSemControl.findCode dest regs code = some prog) :
    ∃ key, sptLookup key code = some prog := by
  cases dest with
  | inl key => exact ⟨key, found⟩
  | inr reg =>
    simp only [StackSemControl.findCode] at found
    split at found
    · rename_i key read
      exact ⟨key, found⟩
    · contradiction

theorem executionComplete_tail {F : Type} (dest : Sum Nat Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (ih : ExecutionCompleteIH (.call none dest none) source) :
    ExecutionCompleteAt (.call none dest none) source := by
  intro result post run valid supported global scope
  have rootRun := run
  rw [StackSemEvaluate.evaluate_call] at run
  cases found : StackSemControl.findCode dest source.regs source.code with
  | none =>
    simp only [found] at run
    obtain ⟨rfl, _⟩ := Prod.mk.inj run
    exact False.elim valid
  | some prog =>
    simp only [found] at run
    by_cases zero : source.clock = 0
    · rw [if_pos zero] at run
      obtain ⟨rfl, _⟩ := Prod.mk.inj run
      exact False.elim valid
    · rw [if_neg zero, StackSemEvaluateClock.fixClockEvaluate] at run
      rcases bodyRun : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock source) with ⟨bodyResult, middle⟩
      rw [bodyRun] at run
      dsimp only at run
      by_cases bad : StackSemControl.badFunReturn bodyResult = true
      · rw [if_pos bad] at run
        obtain ⟨rfl, _⟩ := Prod.mk.inj run
        exact False.elim valid
      · rw [if_neg bad] at run
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
        obtain ⟨key, lookup⟩ := execution_findCode_lookup found
        have smaller : StackSemMeasure.LexNat
            ((StackSemStateOps.decClock source).clock, sizeOf prog)
            (source.clock, sizeOf (.call none dest none : HolProg 64)) := by
          apply Prod.Lex.left
          change source.clock - 1 < source.clock
          omega
        have tree := ih prog _ smaller bodyResult middle bodyRun valid
          (global key prog lookup) global (ExecutionLabelScope.of_lookup lookup)
        have nonNormal : executionKindOfResult bodyResult ≠ .normal := by
          cases bodyResult with
          | none => exact False.elim (bad rfl)
          | some value => exact executionKindOfResult_nonNormal value
        exact ExecutionTrace.callTail
          (by simpa only [executionKindOfResult_result] using rootRun) zero found nonNormal tree

#print axioms execution_findCode_lookup
#print axioms executionComplete_tail
end InitECandidate.Runtime.StackToLab
