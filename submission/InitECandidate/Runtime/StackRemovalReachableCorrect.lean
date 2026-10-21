import InitECandidate.Runtime.StackRemovalPriceCaps
import InitECandidate.Runtime.StackDirectCallClosure
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

/-- Only allowed direct callees need a quantitative compiler proof. An
installed but syntactically unreachable excluded label remains untouched. -/
def AvoidingRemovalCode (forbidden : Nat) (code : Spt (HolProg 64)) : Prop :=
  ∀ key p, sptLookup key code = some p → key ≠ forbidden →
    removalSupported p = true ∧ directCallsAvoid forbidden p = true

theorem avoidingRemovalCode_evaluate {C F : Type} {forbidden : Nat} (p : HolProg 64)
    (source post : StackSemStateFiniteExact 64 C F) result
    (oracle : EmptyInstallOracle source) (global : AvoidingRemovalCode forbidden source.code)
    (run : StackSemEvaluate.evaluate (p, source) = (result, post)) :
    AvoidingRemovalCode forbidden post.code ∧ EmptyInstallOracle post := by
  obtain ⟨code, postOracle⟩ := evaluate_emptyInstallOracle p source post result oracle run
  exact ⟨code ▸ global, postOracle⟩

private theorem reachableRemoval_smaller {F : Type} (p q : HolProg 64)
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
theorem stackRemoval_cost_correct_reachableWithPrice {F : Type} (forbidden : Nat)
    (sourcePrice targetPrice : HolProg 64 → Nat)
    (bounds : BitVec 64 × BitVec 64) (caps : RemovalPriceCaps (F := F) sourcePrice targetPrice bounds)
    (p : HolProg 64) (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (supported : removalSupported p = true) (closed : directCallsAvoid forbidden p = true)
    (global : AvoidingRemovalCode forbidden source.code)
    (oracle : EmptyInstallOracle source) :
    RemovalCostSimulationFor sourcePrice targetPrice false bounds p source := by
  have ih : ∀ q (child : StackSemStateFiniteExact 64 LabToTarget.Config F),
      StackSemMeasure.LexNat (child.clock, sizeOf q) (source.clock, sizeOf p) →
      removalSupported q = true → directCallsAvoid forbidden q = true →
      AvoidingRemovalCode forbidden child.code → EmptyInstallOracle child →
      RemovalCostSimulationFor sourcePrice targetPrice false bounds q child := by
    intro q child smaller eligibility closedChild code oracleChild
    exact stackRemoval_cost_correct_reachableWithPrice forbidden sourcePrice targetPrice bounds caps q child eligibility closedChild code oracleChild
  by_cases leaf : removalLeaf p = true
  · exact caps.leaf p source supported leaf
  · cases p <;> try (solve | simp [removalLeaf] at leaf)
    case seq first second =>
      simp only [removalSupported, Bool.and_eq_true] at supported
      simp only [directCallsAvoid, Bool.and_eq_true] at closed
      apply removalCostSimulation_seqWithPrice sourcePrice targetPrice caps.freeSeq false bounds first second source
      · exact ih first source (Prod.Lex.right _ (by simp; omega)) supported.1 closed.1 global oracle
      · intro middle firstRun
        obtain ⟨code, postOracle⟩ := avoidingRemovalCode_evaluate first source middle none oracle global firstRun
        exact ih second middle (reachableRemoval_smaller _ _ source middle
          (StackSemEvaluateClock.evaluateClock first source none middle firstRun) (by simp)) supported.2 closed.2 code postOracle
    case ite cmp reg operand yes no =>
      simp only [removalSupported, Bool.and_eq_true] at supported
      simp only [directCallsAvoid, Bool.and_eq_true] at closed
      apply removalCostSimulation_iteWithPrice sourcePrice targetPrice false bounds cmp reg operand yes no (caps.branch cmp reg operand yes no) source
      · exact ih yes source (Prod.Lex.right _ (by simp; omega)) supported.1 closed.1 global oracle
      · exact ih no source (Prod.Lex.right _ (by simp)) supported.2 closed.2 global oracle
    case loop body =>
      have bodySupported : removalSupported body = true := by simpa only [removalSupported] using supported
      have bodyClosed : directCallsAvoid forbidden body = true := by simpa only [directCallsAvoid] using closed
      apply removalCostSimulation_loopWithPrice sourcePrice targetPrice false bounds body (fun pointer => caps.loopNode body (StackRemove.comp false bounds pointer body)) source
      · exact ih body source (Prod.Lex.right _ (by simp)) bodySupported bodyClosed global oracle
      · intro bodyResult middle bodyRun continues positive
        obtain ⟨code, postOracle⟩ := avoidingRemovalCode_evaluate body source middle bodyResult oracle global bodyRun
        have clockLe := StackSemEvaluateClock.evaluateClock body source bodyResult middle bodyRun
        have smaller : (decClock middle).clock < source.clock := by
          change middle.clock - 1 < source.clock
          omega
        exact ih (.loop body) _ (Prod.Lex.left _ _ smaller) supported closed code postOracle
    case rawCall label =>
      apply removalCostSimulation_rawWithPrice sourcePrice targetPrice false bounds label (caps.raw label) source
      intro frame body found positive
      have eligibility := global label (.seq frame body) found (by simpa only [directCallsAvoid, decide_eq_true_eq] using closed)
      simp only [removalSupported, directCallsAvoid, Bool.and_eq_true] at eligibility
      have smaller : (decClock source).clock < source.clock := by
        change source.clock - 1 < source.clock
        omega
      exact ih body _ (Prod.Lex.left _ _ smaller) eligibility.1.2 eligibility.2.2 global oracle
    case call ret dest handler =>
      obtain ⟨label, rfl, allowed⟩ := directCallsAvoid_direct closed
      cases ret with
      | none =>
        apply removalCostSimulation_tailWithPrice sourcePrice targetPrice false bounds (.inl label) handler (caps.tail (.inl label) handler) source
        intro program found noHandler positive
        have lookup : sptLookup label source.code = some program := by
          simpa only [StackSemControl.findCode] using found
        have eligibility := global label program lookup allowed
        have smaller : (decClock source).clock < source.clock := by
          change source.clock - 1 < source.clock
          omega
        exact ih program _ (Prod.Lex.left _ _ smaller) eligibility.1 eligibility.2 global oracle
      | some packet =>
        rcases packet with ⟨body, link, l1, l2⟩
        have entrySmall (positive : source.clock ≠ 0) :
            (decClock (setVar link (.loc l1 l2) source)).clock < source.clock := by
          change source.clock - 1 < source.clock
          omega
        have callee program (found : StackSemControl.findCode (.inl label) (source.regs.eraseEq link) source.code = some program)
            (positive : source.clock ≠ 0) :
            RemovalCostSimulationFor sourcePrice targetPrice false bounds program
              (decClock (setVar link (.loc l1 l2) source)) := by
          have lookup : sptLookup label source.code = some program := by
            simpa only [StackSemControl.findCode] using found
          have eligibility := global label program lookup allowed
          exact ih program _ (Prod.Lex.left _ _ (entrySmall positive)) eligibility.1 eligibility.2 global oracle
        cases handler with
        | none =>
          have bodyClosed : directCallsAvoid forbidden body = true := by
            have check := closed
            simp only [directCallsAvoid, Bool.and_eq_true, Bool.and_true, decide_eq_true_eq] at check
            exact check.2
          have bodySupported : removalSupported body = true := by simpa only [removalSupported, Bool.and_true] using supported
          apply removalCostSimulation_returnNoneWithPrice sourcePrice targetPrice false bounds body link l1 l2 (.inl label) (fun pointer => caps.returning body link l1 l2 (.inl label) none (StackRemove.comp false bounds pointer body) none) source callee
          intro program middle found positive bodyRun
          obtain ⟨code, postOracle⟩ := avoidingRemovalCode_evaluate program (decClock (setVar link (.loc l1 l2) source)) middle _ oracle global bodyRun
          have smaller := Nat.lt_of_le_of_lt (StackSemEvaluateClock.evaluateClock _ _ _ _ bodyRun) (entrySmall positive)
          exact ih body middle (Prod.Lex.left _ _ smaller) bodySupported bodyClosed code postOracle
        | some handlerPacket =>
          rcases handlerPacket with ⟨hp, hs, hl⟩
          have pairClosed : directCallsAvoid forbidden body = true ∧ directCallsAvoid forbidden hp = true := by
            have check := closed
            simp only [directCallsAvoid, Bool.and_eq_true, decide_eq_true_eq] at check
            exact ⟨check.1.2, check.2⟩
          have pairSupported : removalSupported body = true ∧ removalSupported hp = true := by
            simpa only [removalSupported, Bool.and_eq_true] using supported
          apply removalCostSimulation_returnHandlerWithPrice sourcePrice targetPrice false bounds body hp link l1 l2 hs hl (.inl label) (fun pointer => caps.returning body link l1 l2 (.inl label) (some (hp,hs,hl)) (StackRemove.comp false bounds pointer body) (some (StackRemove.comp false bounds pointer hp,hs,hl))) source callee
          · intro program middle found positive bodyRun
            obtain ⟨code, postOracle⟩ := avoidingRemovalCode_evaluate program (decClock (setVar link (.loc l1 l2) source)) middle _ oracle global bodyRun
            have smaller := Nat.lt_of_le_of_lt (StackSemEvaluateClock.evaluateClock _ _ _ _ bodyRun) (entrySmall positive)
            exact ih body middle (Prod.Lex.left _ _ smaller) pairSupported.1 pairClosed.1 code postOracle
          · intro program middle found positive bodyRun
            obtain ⟨code, postOracle⟩ := avoidingRemovalCode_evaluate program (decClock (setVar link (.loc l1 l2) source)) middle _ oracle global bodyRun
            have smaller := Nat.lt_of_le_of_lt (StackSemEvaluateClock.evaluateClock _ _ _ _ bodyRun) (entrySmall positive)
            exact ih hp middle (Prod.Lex.left _ _ smaller) pairSupported.2 pairClosed.2 code postOracle
termination_by (source.clock, sizeOf p)
decreasing_by exact smaller

/-- Conservative-table specialization with the same excluded-code closure. -/
theorem stackRemoval_cost_correct_reachable {F : Type} (forbidden gap : Nat) (bounds : BitVec 64 × BitVec 64)
    (p : HolProg 64) (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (supported : removalSupported p = true) (closed : directCallsAvoid forbidden p = true)
    (global : AvoidingRemovalCode forbidden source.code)
    (oracle : EmptyInstallOracle source) :
    RemovalCostSimulation (removalLocalPrice gap bounds) gap false bounds p source :=
  stackRemoval_cost_correct_reachableWithPrice forbidden _ _ bounds
    (conservativeRemovalPriceCaps gap bounds) p source supported closed global oracle

#print axioms stackRemoval_cost_correct_reachableWithPrice
#print axioms stackRemoval_cost_correct_reachable
end InitECandidate.Runtime.StackToLab
