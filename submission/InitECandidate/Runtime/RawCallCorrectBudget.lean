import InitECandidate.Runtime.RawCallCallBudget
import InitECandidate.Runtime.RawCallLoopBudget
import InitECandidate.Runtime.RawCallSeqCorrect
import InitECandidate.Runtime.RawCallZeroBudget
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall Flapjack.StackSemMeasure
open Flapjack.StackSemStateOps Flapjack.StackSemControl

/-- Whole RawCall quantitative simulation at the evaluator's actual recursive
sites. All original relation and timeout/stack-overflow exceptions are retained. -/
theorem compCorrectMeasure {width : Nat} [NeZero width] {C F : Type} :
    ∀ (measure : Nat × Nat) (program : HolProg width)
      (source : StackSemStateFiniteExact width C F),
      stackSemMeasure program source = measure →
      ∀ (info : Spt Nat) (target post : StackSemStateFiniteExact width C F)
        (result : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (program, source) = (result, post) ∧
        result ≠ some .error ∧ stateRel info source target →
      BoundedSimulationResult (compTop info program) info target post result
        (clockAllowance program source.clock post.clock) ∧
      BoundedSimulationResult (comp info program) info target post result
        (clockAllowance program source.clock post.clock) := by
  intro measure
  induction measure using StackProps.EvaluateAddClock.lexNat_wf.induction with
  | _ measure ih =>
  intro p s hm info t post r hypothesis
  subst hm
  by_cases leaf : zeroClockLeaf p = true
  · obtain ⟨top, body⟩ := zeroClockLeaf_correct p s t post info r leaf hypothesis
    exact ⟨top.mono (Nat.zero_le _), body.mono (Nat.zero_le _)⟩
  cases p
  all_goals try exact (leaf (by rfl)).elim
  case seq first second =>
    apply compCorrectSeq first second info s t post r
    · intro i target out res h
      exact (ih _ (seq_first_measure_lt first second s) first s rfl i target out res h).2
    · intro middle firstRun i target out res h
      have bound := StackSemEvaluateClock.evaluateClock first s none middle firstRun
      exact (ih _ (lexNat_of_le_of_size_lt bound (seq_second_size_lt first second))
        second middle rfl i target out res h).2
    · exact hypothesis
  case ite cmp reg operand first second =>
    apply compCorrectIf cmp reg operand first second info s t post r
    · intro x y left right compared i target out res h
      exact (ih _ (if_first_measure_lt cmp reg operand first second s)
        first s rfl i target out res h).2
    · intro x y left right compared i target out res h
      exact (ih _ (if_second_measure_lt cmp reg operand first second s)
        second s rfl i target out res h).2
    · exact hypothesis
  case loop body =>
    apply compCorrectLoop body info s t post r
    · intro i target out res h
      exact (ih _ (loop_body_measure_lt body s) body s rfl i target out res h).2
    · intro bodyResult middle bodyRun continues nonzero i target out res h
      have lower := LoopCase.loopReentryClockLess body s middle bodyResult bodyRun nonzero
      exact (ih _ (lexNat_of_clock_lt lower) (.loop body) (decClock middle)
        rfl i target out res h).2
    · exact hypothesis
  case jumpLower r1 r2 dest =>
    apply compCorrectJumpLower r1 r2 dest info s t post r
    · intro x y prog left right compared lookup nonzero i target out res h
      exact (ih _ (callee_measure_lt prog (.jumpLower r1 r2 dest) s nonzero)
        prog (decClock s) rfl i target out res h).1
    · exact hypothesis
  case rawCall dest =>
    apply compCorrectRawCall dest info s t post r
    · intro first body lookup nonzero i target out res h
      exact (ih _ (callee_measure_lt body (.rawCall dest) s nonzero)
        body (decClock s) rfl i target out res h).2
    · exact hypothesis
  case call ret dest handler =>
    apply compCorrectCall ret dest handler info s t post r
    · cases ret with
      | none =>
        intro absent prog lookup nonzero i target out res h
        exact (ih _ (callee_measure_lt prog (.call none dest handler) s nonzero)
          prog (decClock s) rfl i target out res h).1
      | some triple =>
        obtain ⟨body, link, l1, l2⟩ := triple
        refine ⟨?_, ?_, ?_⟩
        · intro prog lookup nonzero i target out res h
          have lower := callee_measure_lt prog (.call (some (body, link, l1, l2)) dest handler)
            (setVar link (.loc l1 l2) s) nonzero
          exact (ih _ lower prog (decClock (setVar link (.loc l1 l2) s))
            rfl i target out res h).1
        · intro prog lookup nonzero middle calleeRun i target out res h
          have bound := StackSemEvaluateClock.evaluateClock prog
            (decClock (setVar link (.loc l1 l2) s)) _ middle calleeRun
          have lower : middle.clock < s.clock := by
            have decreased := decClock_clock_lt (setVar link (.loc l1 l2) s) nonzero
            exact Nat.lt_of_le_of_lt bound decreased
          exact (ih _ (lexNat_of_clock_lt lower) body middle rfl i target out res h).2
        · intro prog handlerBody hl1 hl2 lookup nonzero present middle calleeRun i target out res h
          have bound := StackSemEvaluateClock.evaluateClock prog
            (decClock (setVar link (.loc l1 l2) s)) _ middle calleeRun
          have lower : middle.clock < s.clock := by
            have decreased := decClock_clock_lt (setVar link (.loc l1 l2) s) nonzero
            exact Nat.lt_of_le_of_lt bound decreased
          exact (ih _ (lexNat_of_clock_lt lower) handlerBody middle rfl i target out res h).2
    · exact hypothesis


/-- All programs, with no recursive simulation premise. The extra clock is at
most actual source clock consumption, reserving one tick for Call syntax. -/
theorem compCorrect_bounded {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (source target post : StackSemStateFiniteExact width C F)
    (info : Spt Nat) (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (program, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulationResult (compTop info program) info target post result
      (clockAllowance program source.clock post.clock) ∧
    BoundedSimulationResult (comp info program) info target post result
      (clockAllowance program source.clock post.clock) :=
  compCorrectMeasure (stackSemMeasure program source) program source rfl info target post result hypothesis

#print axioms compCorrect_bounded
end InitECandidate.Runtime.StackRawCall
