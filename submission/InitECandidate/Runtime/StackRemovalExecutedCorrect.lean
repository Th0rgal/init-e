import InitECandidate.Runtime.StackRemovalLeafSimulation
import InitECandidate.Runtime.StackRemoveExecutedConditional
import InitECandidate.Runtime.StackRemoveExecutedLoop
import InitECandidate.Runtime.StackRemoveExecutedTail
import InitECandidate.Runtime.StackRemoveExecutedRaw
import InitECandidate.Runtime.StackRemoveExecutedReturnNone
import InitECandidate.Runtime.StackRemoveExecutedReturnHandler
import InitECandidate.Runtime.StackExecutionCompleteTail
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps

private theorem removal_smaller {F : Type} (p q : HolProg 64)
    (source child : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (clock : child.clock ≤ source.clock) (size : sizeOf q < sizeOf p) :
    StackSemMeasure.LexNat (child.clock, sizeOf q) (source.clock, sizeOf p) := by
  rcases Nat.lt_or_eq_of_le clock with lt | eq
  · exact Prod.Lex.left _ _ lt
  · rw [eq]; exact Prod.Lex.right _ size

/-- Whole supported stack-removal execution-cost transfer. The original
semantic premises derive a compiled evaluator run whose executed native-priced
work is at most the size-sensitive source work. No target run or cost bound
is assumed. The closed installation oracle preserves callee eligibility. -/
theorem stackRemoval_cost_correct {F : Type} (gap : Nat) (bounds : BitVec 64 × BitVec 64)
    (p : HolProg 64) (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (supported : removalSupported p = true) (global : RemovalCodeSupported source.code)
    (oracle : EmptyInstallOracle source) :
    RemovalCostSimulation (removalLocalPrice gap bounds) gap false bounds p source := by
  have ih : ∀ q (child : StackSemStateFiniteExact 64 LabToTarget.Config F),
      StackSemMeasure.LexNat (child.clock, sizeOf q) (source.clock, sizeOf p) →
      removalSupported q = true → RemovalCodeSupported child.code → EmptyInstallOracle child →
      RemovalCostSimulation (removalLocalPrice gap bounds) gap false bounds q child := by
    intro q child smaller eligibility code oracleChild
    exact stackRemoval_cost_correct gap bounds q child eligibility code oracleChild
  by_cases leaf : removalLeaf p = true
  · exact removalCostSimulation_leaf gap bounds p source supported leaf
  · cases p <;> try (solve | simp [removalLeaf] at leaf)
    case seq first second =>
      simp only [removalSupported, Bool.and_eq_true] at supported
      apply removalCostSimulation_seq _ gap false bounds first second source
      · exact ih first source (Prod.Lex.right _ (by simp; omega)) supported.1 global oracle
      · intro middle firstRun
        obtain ⟨code, postOracle⟩ := removalCodeSupported_evaluate first source middle none oracle global firstRun
        exact ih second middle (removal_smaller _ _ source middle
          (StackSemEvaluateClock.evaluateClock first source none middle firstRun) (by simp)) supported.2 code postOracle
    case ite cmp reg operand yes no =>
      simp only [removalSupported, Bool.and_eq_true] at supported
      apply removalCostSimulation_ite _ gap false bounds cmp reg operand yes no (Nat.le_refl _) source
      · exact ih yes source (Prod.Lex.right _ (by simp; omega)) supported.1 global oracle
      · exact ih no source (Prod.Lex.right _ (by simp)) supported.2 global oracle
    case loop body =>
      have bodySupported : removalSupported body = true := by simpa only [removalSupported] using supported
      apply removalCostSimulation_loop _ gap false bounds body (Nat.le_refl _) source
      · exact ih body source (Prod.Lex.right _ (by simp)) bodySupported global oracle
      · intro bodyResult middle bodyRun continues positive
        obtain ⟨code, postOracle⟩ := removalCodeSupported_evaluate body source middle bodyResult oracle global bodyRun
        have clockLe := StackSemEvaluateClock.evaluateClock body source bodyResult middle bodyRun
        have smaller : (decClock middle).clock < source.clock := by
          change middle.clock - 1 < source.clock
          omega
        exact ih (.loop body) _ (Prod.Lex.left _ _ smaller) supported code postOracle
    case rawCall label =>
      apply removalCostSimulation_raw _ gap false bounds label (Nat.le_refl _) source
      intro frame body found positive
      have eligibility := global label (.seq frame body) found
      simp only [removalSupported, Bool.and_eq_true] at eligibility
      have smaller : (decClock source).clock < source.clock := by
        change source.clock - 1 < source.clock
        omega
      exact ih body _ (Prod.Lex.left _ _ smaller) eligibility.2 global oracle
    case call ret dest handler =>
      cases ret with
      | none =>
        apply removalCostSimulation_tail _ gap false bounds dest handler (Nat.le_refl _) source
        intro program found noHandler positive
        obtain ⟨key, lookup⟩ := execution_findCode_lookup found
        have smaller : (decClock source).clock < source.clock := by
          change source.clock - 1 < source.clock
          omega
        exact ih program _ (Prod.Lex.left _ _ smaller) (global key program lookup) global oracle
      | some packet =>
        rcases packet with ⟨body, link, l1, l2⟩
        have entrySmall (positive : source.clock ≠ 0) :
            (decClock (setVar link (.loc l1 l2) source)).clock < source.clock := by
          change source.clock - 1 < source.clock
          omega
        have callee program (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program)
            (positive : source.clock ≠ 0) :
            RemovalCostSimulation (removalLocalPrice gap bounds) gap false bounds program
              (decClock (setVar link (.loc l1 l2) source)) := by
          obtain ⟨key, lookup⟩ := execution_findCode_lookup found
          exact ih program _ (Prod.Lex.left _ _ (entrySmall positive)) (global key program lookup) global oracle
        cases handler with
        | none =>
          have bodySupported : removalSupported body = true := by simpa only [removalSupported, Bool.and_true] using supported
          apply removalCostSimulation_returnNone _ gap false bounds body link l1 l2 dest (Nat.le_refl _) source callee
          intro program middle found positive bodyRun
          obtain ⟨code, postOracle⟩ := removalCodeSupported_evaluate program (decClock (setVar link (.loc l1 l2) source)) middle _ oracle global bodyRun
          have smaller := Nat.lt_of_le_of_lt (StackSemEvaluateClock.evaluateClock _ _ _ _ bodyRun) (entrySmall positive)
          exact ih body middle (Prod.Lex.left _ _ smaller) bodySupported code postOracle
        | some handlerPacket =>
          rcases handlerPacket with ⟨hp, hs, hl⟩
          have pairSupported : removalSupported body = true ∧ removalSupported hp = true := by
            simpa only [removalSupported, Bool.and_eq_true] using supported
          apply removalCostSimulation_returnHandler _ gap false bounds body hp link l1 l2 hs hl dest (Nat.le_refl _) source callee
          · intro program middle found positive bodyRun
            obtain ⟨code, postOracle⟩ := removalCodeSupported_evaluate program (decClock (setVar link (.loc l1 l2) source)) middle _ oracle global bodyRun
            have smaller := Nat.lt_of_le_of_lt (StackSemEvaluateClock.evaluateClock _ _ _ _ bodyRun) (entrySmall positive)
            exact ih body middle (Prod.Lex.left _ _ smaller) pairSupported.1 code postOracle
          · intro program middle found positive bodyRun
            obtain ⟨code, postOracle⟩ := removalCodeSupported_evaluate program (decClock (setVar link (.loc l1 l2) source)) middle _ oracle global bodyRun
            have smaller := Nat.lt_of_le_of_lt (StackSemEvaluateClock.evaluateClock _ _ _ _ bodyRun) (entrySmall positive)
            exact ih hp middle (Prod.Lex.left _ _ smaller) pairSupported.2 code postOracle
termination_by (source.clock, sizeOf p)
decreasing_by exact smaller

#print axioms stackRemoval_cost_correct
end InitECandidate.Runtime.StackToLab
