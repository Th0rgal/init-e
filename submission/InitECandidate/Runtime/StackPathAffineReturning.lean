import InitECandidate.Runtime.StackPathAffineCalls
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect

theorem affine_return_funding (rate fuel middle post bodyWork contWork bodySize contSize parentSize : Nat)
    (positive : fuel ≠ 0) (bodyClock : middle ≤ fuel - 1) (contClock : post ≤ middle)
    (bodyBound : bodyWork ≤ rate * ((fuel - 1) - middle) + 2 * bodySize)
    (contBound : contWork ≤ rate * (middle - post) + 2 * contSize)
    (funding : 2 * bodySize + 2 ≤ rate) (syntaxBound : contSize ≤ parentSize) :
    bodyWork + contWork + 2 ≤ rate * (fuel - post) + 2 * parentSize := by
  have elapsed : fuel - post = 1 + ((fuel - 1) - middle) + (middle - post) := by omega
  rw [elapsed, Nat.mul_add, Nat.mul_add, Nat.mul_one]
  omega

/-- Every smaller actual execution receives its affine bound from the whole
well-founded induction, together with its preserved code-size invariant. -/
abbrev AffineIH {width : Nat} [NeZero width] {C F : Type} (rate limit : Nat)
    (parent : HolProg width) (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ child next, MeasureLt child next parent source → sizeOf child ≤ limit →
    CodeSizeState limit next → AffinePathBound rate child next

/-- Returning calls pay for the callee and only their valid reached continuation.
The source call tick funds callee syntax; the continuation retains caller potential. -/
theorem pathWork_return_affine {width : Nat} [NeZero width] {C F : Type}
    (rate limit : Nat) (rp : HolProg width) (link l1 l2 : Nat) (dest : Nat ⊕ Nat)
    (handler : Option (HolProg width × Nat × Nat)) (s : StackSemStateFiniteExact width C F)
    (rateEnough : 2 * limit + 2 ≤ rate)
    (sizeBound : sizeOf (.call (some (rp,link,l1,l2)) dest handler : HolProg width) ≤ limit)
    (bounded : CodeSizeState limit s)
    (ih : AffineIH rate limit (.call (some (rp,link,l1,l2)) dest handler) s) :
    AffinePathBound rate (.call (some (rp,link,l1,l2)) dest handler) s := by
  intro result post run notError
  have err : ∀ {bad : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, bad) = (result, post) → False :=
    fun eq => notError (Prod.mk.inj eq).1.symm
  rw [StackSemEvaluate.evaluate_call] at run
  dsimp only at run
  cases found : findCode dest (s.regs.eraseEq link) s.code with
  | none => rw [found] at run; exact (err run).elim
  | some body =>
    rw [found] at run
    dsimp only at run
    by_cases zero : s.clock = 0
    · rw [if_pos zero] at run
      simp only [Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      rw [pathWork, if_pos zero]
      have positive := prog_size_positive (.call (some (rp,link,l1,l2)) dest handler : HolProg width)
      omega
    · rw [if_neg zero, StackSemEvaluateClock.fixClockEvaluate] at run
      let entry := decClock (Flapjack.StackSemStateOps.setVar link (.loc l1 l2) s)
      cases bodyRun : StackSemEvaluate.evaluate (body, entry) with
      | mk bodyResult middle =>
        rw [bodyRun] at run
        have actualBodyRun : StackSemEvaluate.evaluate
            (body, decClock (Flapjack.StackSemStateOps.setVar link (.loc l1 l2) s)) = (bodyResult, middle) := bodyRun
        have bodyNotError : bodyResult ≠ some .error := by
          intro eq
          rw [eq] at run
          exact (err run)
        have entryLt : entry.clock < s.clock := by simp only [entry, decClock, setVar]; omega
        have entryBound : CodeSizeState limit entry := (bounded.setVar link (.loc l1 l2)).decClock
        have bodySize := findCode_size s bounded dest (s.regs.eraseEq link) body found
        have bodyBound := ih body entry (.inl entryLt) bodySize entryBound
          bodyResult middle bodyRun bodyNotError
        have middleClock := StackSemEvaluateClock.evaluateClock body entry bodyResult middle bodyRun
        have clockBound : middle.clock ≤ s.clock - 1 := middleClock
        have middleLt : middle.clock < s.clock := Nat.lt_of_le_of_lt middleClock entryLt
        have middleBound := CodeSizeState.of_evaluate bodyRun entryBound
        have funding : 2 * sizeOf body + 2 ≤ rate := by omega
        rw [pathWork, if_neg zero, found]
        dsimp only
        simp only [StackSemEvaluateClock.fixClockEvaluate]
        simp only [actualBodyRun]
        change pathWork body entry + selectedContinuationBudget bodyResult l1 l2 handler
          (pathWork rp middle)
          (match (generalizing := false) handler with | none => 0 | some (hp,_,_) => pathWork hp middle) + 2 ≤ _
        cases bodyResult with
        | none => exact (err run).elim
        | some value =>
          cases value
          case result location =>
            dsimp only at run
            by_cases same : location = .loc l1 l2
            · rw [if_neg (not_not.mpr same)] at run
              have syntaxBound : sizeOf rp ≤ sizeOf (.call (some (rp,link,l1,l2)) dest handler : HolProg width) := by
                simp_wf; omega
              have retSize : sizeOf rp ≤ limit := Nat.le_trans syntaxBound sizeBound
              have contBound := ih rp middle (.inl middleLt) retSize middleBound result post run notError
              have contClock := StackSemEvaluateClock.evaluateClock rp middle result post run
              simp only [selectedContinuationBudget, if_pos same]
              exact affine_return_funding rate s.clock middle.clock post.clock _ _ _ _ _ zero
                clockBound contClock bodyBound contBound funding syntaxBound
            · rw [if_pos same] at run
              exact (err run).elim
          case exception location =>
            dsimp only at run
            cases handler with
            | none =>
              simp only [Prod.mk.injEq] at run
              obtain ⟨rfl, rfl⟩ := run
              simp only [selectedContinuationBudget, Nat.add_zero]
              have funded := affine_tick_funding rate s.clock middle.clock _ (sizeOf body) 0 zero
                clockBound bodyBound funding
              omega
            | some desc =>
              rcases desc with ⟨hp, hs, hl⟩
              dsimp only at run
              by_cases same : location = .loc hs hl
              · rw [if_neg (not_not.mpr same)] at run
                have syntaxBound : sizeOf hp ≤ sizeOf
                    (.call (some (rp,link,l1,l2)) dest (some (hp,hs,hl)) : HolProg width) := by
                  simp_wf; omega
                have handlerSize : sizeOf hp ≤ limit := Nat.le_trans syntaxBound sizeBound
                have contBound := ih hp middle (.inl middleLt) handlerSize middleBound result post run notError
                have contClock := StackSemEvaluateClock.evaluateClock hp middle result post run
                simp only [selectedContinuationBudget, if_pos same]
                exact affine_return_funding rate s.clock middle.clock post.clock _ _ _ _ _ zero
                  clockBound contClock bodyBound contBound funding syntaxBound
              · rw [if_pos same] at run
                exact (err run).elim
          case «break» label => exact (err run).elim
          case «continue» label => exact (err run).elim
          case error => exact (bodyNotError rfl).elim
          all_goals
            simp only [Prod.mk.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            simp only [selectedContinuationBudget, Nat.add_zero]
            have funded := affine_tick_funding rate s.clock middle.clock _ (sizeOf body) 0 zero
              clockBound bodyBound funding
            omega

#print axioms affine_return_funding
#print axioms pathWork_return_affine
end InitECandidate.Runtime.StackToLab
