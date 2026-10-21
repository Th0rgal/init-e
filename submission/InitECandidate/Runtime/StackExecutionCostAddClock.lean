import InitECandidate.Runtime.StackExecutionCostClockLocal
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

private theorem costClock_smaller {F : Type} (p q : HolProg 64)
    (source child : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (clock : child.clock ≤ source.clock) (size : sizeOf q < sizeOf p) :
    StackSemMeasure.LexNat (child.clock, sizeOf q) (source.clock, sizeOf p) := by
  rcases Nat.lt_or_eq_of_le clock with lt | eq
  · exact Prod.Lex.left _ _ lt
  · rw [eq]; exact Prod.Lex.right _ size

/-- Adding unused fuel preserves the entire executed Stack cost, for every
actual non-timeout run and every state-independent local price. -/
theorem stackExecutionCost_addClock {F : Type} (price : HolProg 64 → Nat) (p : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) : CostClockStableAt price p source := by
  have ih : ∀ q (child : StackSemStateFiniteExact 64 LabToTarget.Config F),
      StackSemMeasure.LexNat (child.clock, sizeOf q) (source.clock, sizeOf p) → CostClockStableAt price q child := by
    intro q child smaller
    exact stackExecutionCost_addClock price q child
  cases p
  case seq first second =>
    apply costClockStableAt_seq price first second source
    · exact ih first source (Prod.Lex.right _ (by simp; omega))
    · intro middle firstRun
      apply ih second middle
      exact costClock_smaller _ _ source middle
        (StackSemEvaluateClock.evaluateClock first source none middle firstRun) (by simp; omega)
  case ite cmp reg operand yes no =>
    apply costClockStableAt_ite price cmp reg operand yes no source
    · exact ih yes source (Prod.Lex.right _ (by simp; omega))
    · exact ih no source (Prod.Lex.right _ (by simp; omega))
  case loop body =>
    intro post result run notTimeout extra
    apply stackCost_addClock_loop price body source post result run notTimeout _ _ extra
    · intro middle bodyResult bodyRun bodyNotTimeout added
      exact ih body source (Prod.Lex.right _ (by simp)) middle bodyResult bodyRun bodyNotTimeout added
    · intro middle bodyResult bodyRun continues positive restRun added
      have clockLe := StackSemEvaluateClock.evaluateClock body source bodyResult middle bodyRun
      have smaller : (StackSemStateOps.decClock middle).clock < source.clock := by
        change middle.clock - 1 < source.clock
        omega
      exact ih (.loop body) _ (Prod.Lex.left _ _ smaller) post result restRun notTimeout added
  case call ret dest handler =>
    cases ret with
    | none =>
      cases handler with
      | some packet =>
        intro post result run notTimeout extra
        simp only [stackExecutionCost.eq_6, Option.isSome_some, ↓reduceIte]
      | none =>
        intro post result run notTimeout extra
        apply stackCost_addClock_tail price dest source post result run notTimeout _ extra
        intro body middle bodyResult found positive bodyRun bodyNotTimeout added
        have smaller : (StackSemStateOps.decClock source).clock < source.clock := by
          change source.clock - 1 < source.clock
          omega
        exact ih body _ (Prod.Lex.left _ _ smaller) middle bodyResult bodyRun bodyNotTimeout added
    | some packet =>
      rcases packet with ⟨rp, link, l1, l2⟩
      apply stackCost_addClock_return price rp link l1 l2 dest handler source
      intro q child smaller
      exact ih q child (Prod.Lex.left _ _ smaller)
  case rawCall dest =>
    intro post result run notTimeout extra
    apply stackCost_addClock_raw price dest source post result run notTimeout _ extra
    intro prologue body middle bodyResult found positive bodyRun bodyNotTimeout added
    have smaller : (StackSemStateOps.decClock source).clock < source.clock := by
      change source.clock - 1 < source.clock
      omega
    exact ih body _ (Prod.Lex.left _ _ smaller) middle bodyResult bodyRun bodyNotTimeout added
  case jumpLower regX regY dest =>
    apply stackCost_addClock_jump price regX regY dest source
    intro q child smaller
    exact ih q child (Prod.Lex.left _ _ smaller)
  all_goals intro post result run notTimeout extra
  all_goals simp [stackExecutionCost]
termination_by (source.clock, sizeOf p)
decreasing_by exact smaller

#print axioms stackExecutionCost_addClock
end InitECandidate.Runtime.StackToLab
