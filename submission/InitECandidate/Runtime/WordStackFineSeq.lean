import InitECandidate.Runtime.WordStackExecutedSeq
import InitECandidate.Runtime.WordExecutionCostProps
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Runtime.FineCost

/-- Sequence transfer follows the source's executed suffix exactly. In
particular, an early return pays no cost for the unexecuted second statement.
The coefficient is unchanged by composition. -/
theorem executedSimulation_seq {F : Type} (ac : AsmConfigExact 64)
    (price : WordLangProgHOL (BitVec 64) →
      WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F → Nat)
    (factor : Nat) (first second : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (free : price (.seq first second) source = 0)
    (firstIH : ExecutedSimulation ac first source (factor * wordExecutionCost price first source))
    (secondIH : ∀ middle, WordSemStateFiniteExact.evaluate first source = (none, middle) →
      ExecutedSimulation ac second middle (factor * wordExecutionCost price second middle)) :
    ExecutedSimulation ac (.seq first second) source
      (factor * wordExecutionCost price (.seq first second) source) := by
  rcases actual : WordSemStateFiniteExact.evaluate first source with ⟨result, middle⟩
  have cost := wordExecutionCost_seq price first second source
  rw [free, Nat.zero_add, actual] at cost
  cases result with
  | none =>
    have simulation := ExecutedSeq.compCorrectSeqFirstNone
      (factor * wordExecutionCost price first source)
      (factor * wordExecutionCost price second middle) ac first second source
      ⟨?_, firstIH⟩ (by simp only [actual])
    · simpa only [cost, Nat.mul_add] using simulation
    · intro output post run
      have equal : (output, post) = (none, middle) := run.1.trans actual
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
      exact secondIH _ actual
  | some value =>
    have simulation := ExecutedSeq.compCorrectSeqFirstNonNone
      (factor * wordExecutionCost price first source) ac first second source firstIH
      (by simp only [actual, ne_eq, reduceCtorEq, not_false_eq_true])
    simpa only [cost, Nat.add_zero] using simulation

#print axioms executedSimulation_seq
end InitECandidate.Runtime.WordToStack
