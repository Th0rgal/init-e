import InitECandidate.Runtime.GuestCostOpCompareBody
import InitECandidate.Runtime.GuestCmpWordEval
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {F : Type}

/-- Concrete limb-3-less execution of `u256_lt`: the top limbs differ and
`a3 < b3`, so the first branch returns 1 and the remaining limbs are skipped. -/
theorem u256Lt_run_limb3_less (s : PanSemStateFiniteExact 64 F)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (hA : s.locals.lookup (ofString "a") =
      some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]))
    (hB : s.locals.lookup (ofString "b") =
      some (.rStruct [.val (.word b0), .val (.word b1), .val (.word b2), .val (.word b3)]))
    (hne : a3 ≠ b3) (hlt : a3 < b3) :
    ∃ events, StatementRun s (sourceFunctionBody Guest.guestFn_u256_lt)
      (some (.returned (.val (.word (1 : BitVec 64)))))
      (emptyLocalsHOLFinite s) events := by
  classical
  have ha3 := eval_rfield_four_three s (ofString "a") a0 a1 a2 a3 hA
  have hb3 := eval_rfield_four_three s (ofString "b") b0 b1 b2 b3 hB
  have neGuard := eval_cmp_word_ne_true s _ _ a3 b3 ha3 hb3 hne
  have ltGuard := eval_cmp_word_lt_true s _ _ a3 b3 ha3 hb3 hlt
  have ret1 : StatementRun s (.return (.const (1 : BitVec 64)))
      (some (.returned (.val (.word (1 : BitVec 64))))) (emptyLocalsHOLFinite s)
      (.statement :: (expressionEvents s (.const (1 : BitVec 64)) ++
        [.copy (flattenHOL (.val (.word (1 : BitVec 64)))).length])) :=
    StatementRun.returnValue (expression := .const (1 : BitVec 64))
      (costedExpression_events s _ _ (by simp [expressionValue, evalHOLExact]))
      (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])
  have lowerIte : StatementRun s
      (.ite (.cmp Cmp.lower (.rfield 3 (.var VarKind.local (ofString "a")))
          (.rfield 3 (.var VarKind.local (ofString "b"))))
        (.return (.const (1 : BitVec 64))) .skip)
      (some (.returned (.val (.word (1 : BitVec 64))))) (emptyLocalsHOLFinite s)
      (.statement :: (expressionEvents s _ ++
        (.statement :: (expressionEvents s (.const (1 : BitVec 64)) ++
          [.copy (flattenHOL (.val (.word (1 : BitVec 64)))).length])))) :=
    StatementRun.iteYes (costedExpression_events s _ _ ltGuard) (by decide) ret1
  have limb3Yes : StatementRun s
      (.seq (.ite (.cmp Cmp.lower (.rfield 3 (.var VarKind.local (ofString "a")))
            (.rfield 3 (.var VarKind.local (ofString "b"))))
          (.return (.const (1 : BitVec 64))) .skip)
        (.return (.const (0 : BitVec 64))))
      (some (.returned (.val (.word (1 : BitVec 64))))) (emptyLocalsHOLFinite s) _ :=
    StatementRun.seqStop (second := .return (.const (0 : BitVec 64))) (by simp) lowerIte
  have limb3 : StatementRun s (u256LtLimb 3)
      (some (.returned (.val (.word (1 : BitVec 64))))) (emptyLocalsHOLFinite s) _ :=
    StatementRun.iteYes (costedExpression_events s _ _ neGuard) (by decide) limb3Yes
  rw [source_u256Lt_body]
  exact ⟨_, StatementRun.seqStop (second := _) (by simp) limb3⟩

/-- Limb-3-greater execution of `u256_lt`: the top limbs differ but `a3` is not
lower, so the top branch returns 0. -/
theorem u256Lt_run_limb3_greater (s : PanSemStateFiniteExact 64 F)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (hA : s.locals.lookup (ofString "a") =
      some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]))
    (hB : s.locals.lookup (ofString "b") =
      some (.rStruct [.val (.word b0), .val (.word b1), .val (.word b2), .val (.word b3)]))
    (hne : a3 ≠ b3) (hnotlt : ¬ a3 < b3) :
    ∃ events, StatementRun s (sourceFunctionBody Guest.guestFn_u256_lt)
      (some (.returned (.val (.word (0 : BitVec 64)))))
      (emptyLocalsHOLFinite s) events := by
  classical
  have ha3 := eval_rfield_four_three s (ofString "a") a0 a1 a2 a3 hA
  have hb3 := eval_rfield_four_three s (ofString "b") b0 b1 b2 b3 hB
  have neGuard := eval_cmp_word_ne_true s _ _ a3 b3 ha3 hb3 hne
  have ltValue := eval_cmp_word_true s _ _ a3 b3 ha3 hb3
  have ltGuard : expressionValue s
      (.cmp Cmp.lower (.rfield 3 (.var VarKind.local (ofString "a")))
        (.rfield 3 (.var VarKind.local (ofString "b")))) =
      some (.val (.word (0 : BitVec 64))) := by
    rw [ltValue]
    simp [hnotlt]
  have ret0 : StatementRun s (.return (.const (0 : BitVec 64)))
      (some (.returned (.val (.word (0 : BitVec 64))))) (emptyLocalsHOLFinite s)
      (.statement :: (expressionEvents s (.const (0 : BitVec 64)) ++
        [.copy (flattenHOL (.val (.word (0 : BitVec 64)))).length])) :=
    StatementRun.returnValue (expression := .const (0 : BitVec 64))
      (costedExpression_events s _ _ (by simp [expressionValue, evalHOLExact]))
      (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])
  have lowerIte : StatementRun s
      (.ite (.cmp Cmp.lower (.rfield 3 (.var VarKind.local (ofString "a")))
          (.rfield 3 (.var VarKind.local (ofString "b"))))
        (.return (.const (1 : BitVec 64))) .skip) none s
      (.statement :: (expressionEvents s _ ++ [.statement])) :=
    StatementRun.iteNo (costedExpression_events s _ _ ltGuard) (StatementRun.skip s)
  have limb3Yes : StatementRun s
      (.seq (.ite (.cmp Cmp.lower (.rfield 3 (.var VarKind.local (ofString "a")))
            (.rfield 3 (.var VarKind.local (ofString "b"))))
          (.return (.const (1 : BitVec 64))) .skip)
        (.return (.const (0 : BitVec 64))))
      (some (.returned (.val (.word (0 : BitVec 64))))) (emptyLocalsHOLFinite s) _ :=
    StatementRun.seqNext lowerIte ret0
  have limb3 : StatementRun s (u256LtLimb 3)
      (some (.returned (.val (.word (0 : BitVec 64))))) (emptyLocalsHOLFinite s) _ :=
    StatementRun.iteYes (costedExpression_events s _ _ neGuard) (by decide) limb3Yes
  rw [source_u256Lt_body]
  exact ⟨_, StatementRun.seqStop (second := _) (by simp) limb3⟩

#print axioms u256Lt_run_limb3_greater

#print axioms u256Lt_run_limb3_less
end InitECandidate.Runtime.FineCost
