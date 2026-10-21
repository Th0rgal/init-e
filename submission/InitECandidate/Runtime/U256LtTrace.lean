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

/-- Limb-2-less execution when the top limbs are equal. -/
theorem u256Lt_run_limb2_less (s : PanSemStateFiniteExact 64 F)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (hA : s.locals.lookup (ofString "a") =
      some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]))
    (hB : s.locals.lookup (ofString "b") =
      some (.rStruct [.val (.word b0), .val (.word b1), .val (.word b2), .val (.word b3)]))
    (h3 : a3 = b3) (hne : a2 ≠ b2) (hlt : a2 < b2) :
    ∃ events, StatementRun s (sourceFunctionBody Guest.guestFn_u256_lt)
      (some (.returned (.val (.word (1 : BitVec 64)))))
      (emptyLocalsHOLFinite s) events := by
  classical
  have ha3 := eval_rfield_four_three s (ofString "a") a0 a1 a2 a3 hA
  have hb3 := eval_rfield_four_three s (ofString "b") b0 b1 b2 b3 hB
  have eqGuard := eval_cmp_word_ne_false s _ _ a3 b3 ha3 hb3 h3
  have topIte : StatementRun s (u256LtLimb 3) none s
      (.statement :: (expressionEvents s _ ++ [.statement])) :=
    StatementRun.iteNo (costedExpression_events s _ _ eqGuard) (StatementRun.skip s)
  have ret0 : StatementRun s (.return (.const (0 : BitVec 64)))
      (some (.returned (.val (.word (0 : BitVec 64))))) (emptyLocalsHOLFinite s)
      (.statement :: (expressionEvents s (.const (0 : BitVec 64)) ++
        [.copy (flattenHOL (.val (.word (0 : BitVec 64)))).length])) :=
    StatementRun.returnValue (expression := .const (0 : BitVec 64))
      (costedExpression_events s _ _ (by simp [expressionValue, evalHOLExact]))
      (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])
  have ret1 : StatementRun s (.return (.const (1 : BitVec 64)))
      (some (.returned (.val (.word (1 : BitVec 64))))) (emptyLocalsHOLFinite s)
      (.statement :: (expressionEvents s (.const (1 : BitVec 64)) ++
        [.copy (flattenHOL (.val (.word (1 : BitVec 64)))).length])) :=
    StatementRun.returnValue (expression := .const (1 : BitVec 64))
      (costedExpression_events s _ _ (by simp [expressionValue, evalHOLExact]))
      (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])
  have ha2 := eval_rfield_four_two s (ofString "a") a0 a1 a2 a3 hA
  have hb2 := eval_rfield_four_two s (ofString "b") b0 b1 b2 b3 hB
  have neGuard2 := eval_cmp_word_ne_true s _ _ a2 b2 ha2 hb2 hne
  have ltGuard2 := eval_cmp_word_lt_true s _ _ a2 b2 ha2 hb2 hlt
  have lowerIte : StatementRun s
      (.ite (.cmp Cmp.lower (.rfield 2 (.var VarKind.local (ofString "a")))
          (.rfield 2 (.var VarKind.local (ofString "b"))))
        (.return (.const (1 : BitVec 64))) .skip)
      (some (.returned (.val (.word (1 : BitVec 64))))) (emptyLocalsHOLFinite s) _ :=
    StatementRun.iteYes (costedExpression_events s _ _ ltGuard2) (by decide) ret1
  have limb2Yes : StatementRun s
      (.seq (.ite (.cmp Cmp.lower (.rfield 2 (.var VarKind.local (ofString "a")))
            (.rfield 2 (.var VarKind.local (ofString "b"))))
          (.return (.const (1 : BitVec 64))) .skip)
        (.return (.const (0 : BitVec 64))))
      (some (.returned (.val (.word (1 : BitVec 64))))) (emptyLocalsHOLFinite s) _ :=
    StatementRun.seqStop (second := .return (.const (0 : BitVec 64))) (by simp) lowerIte
  have limb2 : StatementRun s (u256LtLimb 2)
      (some (.returned (.val (.word (1 : BitVec 64))))) (emptyLocalsHOLFinite s) _ :=
    StatementRun.iteYes (costedExpression_events s _ _ neGuard2) (by decide) limb2Yes
  have rest : StatementRun s (.seq (u256LtLimb 2)
      (.seq (u256LtLimb 1) (.seq u256LtFinal (.return (.const (0 : BitVec 64))))))
      (some (.returned (.val (.word (1 : BitVec 64))))) (emptyLocalsHOLFinite s) _ :=
    StatementRun.seqStop (second := _) (by simp) limb2
  rw [source_u256Lt_body]
  exact ⟨_, StatementRun.seqNext topIte rest⟩

#print axioms u256Lt_run_limb2_less

/-- Limb-1-less execution when limbs 3 and 2 are equal. -/
theorem u256Lt_run_limb1_less (s : PanSemStateFiniteExact 64 F)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (hA : s.locals.lookup (ofString "a") =
      some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]))
    (hB : s.locals.lookup (ofString "b") =
      some (.rStruct [.val (.word b0), .val (.word b1), .val (.word b2), .val (.word b3)]))
    (h3 : a3 = b3) (h2 : a2 = b2) (hne : a1 ≠ b1) (hlt : a1 < b1) :
    ∃ events, StatementRun s (sourceFunctionBody Guest.guestFn_u256_lt)
      (some (.returned (.val (.word (1 : BitVec 64)))))
      (emptyLocalsHOLFinite s) events := by
  classical
  have ha3 := eval_rfield_four_three s (ofString "a") a0 a1 a2 a3 hA
  have hb3 := eval_rfield_four_three s (ofString "b") b0 b1 b2 b3 hB
  have eqGuard3 := eval_cmp_word_ne_false s _ _ a3 b3 ha3 hb3 h3
  have skip3 : StatementRun s (u256LtLimb 3) none s
      (.statement :: (expressionEvents s _ ++ [.statement])) :=
    StatementRun.iteNo (costedExpression_events s _ _ eqGuard3) (StatementRun.skip s)
  have ha2 := eval_rfield_four_two s (ofString "a") a0 a1 a2 a3 hA
  have hb2 := eval_rfield_four_two s (ofString "b") b0 b1 b2 b3 hB
  have eqGuard2 := eval_cmp_word_ne_false s _ _ a2 b2 ha2 hb2 h2
  have skip2 : StatementRun s (u256LtLimb 2) none s
      (.statement :: (expressionEvents s _ ++ [.statement])) :=
    StatementRun.iteNo (costedExpression_events s _ _ eqGuard2) (StatementRun.skip s)
  have ret0 : StatementRun s (.return (.const (0 : BitVec 64)))
      (some (.returned (.val (.word (0 : BitVec 64))))) (emptyLocalsHOLFinite s)
      (.statement :: (expressionEvents s (.const (0 : BitVec 64)) ++
        [.copy (flattenHOL (.val (.word (0 : BitVec 64)))).length])) :=
    StatementRun.returnValue (expression := .const (0 : BitVec 64))
      (costedExpression_events s _ _ (by simp [expressionValue, evalHOLExact]))
      (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])
  have ret1 : StatementRun s (.return (.const (1 : BitVec 64)))
      (some (.returned (.val (.word (1 : BitVec 64))))) (emptyLocalsHOLFinite s)
      (.statement :: (expressionEvents s (.const (1 : BitVec 64)) ++
        [.copy (flattenHOL (.val (.word (1 : BitVec 64)))).length])) :=
    StatementRun.returnValue (expression := .const (1 : BitVec 64))
      (costedExpression_events s _ _ (by simp [expressionValue, evalHOLExact]))
      (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])
  have ha1 := eval_rfield_four_one s (ofString "a") a0 a1 a2 a3 hA
  have hb1 := eval_rfield_four_one s (ofString "b") b0 b1 b2 b3 hB
  have neGuard1 := eval_cmp_word_ne_true s _ _ a1 b1 ha1 hb1 hne
  have ltGuard1 := eval_cmp_word_lt_true s _ _ a1 b1 ha1 hb1 hlt
  have lowerIte : StatementRun s
      (.ite (.cmp Cmp.lower (.rfield 1 (.var VarKind.local (ofString "a")))
          (.rfield 1 (.var VarKind.local (ofString "b"))))
        (.return (.const (1 : BitVec 64))) .skip)
      (some (.returned (.val (.word (1 : BitVec 64))))) (emptyLocalsHOLFinite s) _ :=
    StatementRun.iteYes (costedExpression_events s _ _ ltGuard1) (by decide) ret1
  have limb1Yes : StatementRun s
      (.seq (.ite (.cmp Cmp.lower (.rfield 1 (.var VarKind.local (ofString "a")))
            (.rfield 1 (.var VarKind.local (ofString "b"))))
          (.return (.const (1 : BitVec 64))) .skip)
        (.return (.const (0 : BitVec 64))))
      (some (.returned (.val (.word (1 : BitVec 64))))) (emptyLocalsHOLFinite s) _ :=
    StatementRun.seqStop (second := .return (.const (0 : BitVec 64))) (by simp) lowerIte
  have limb1 : StatementRun s (u256LtLimb 1)
      (some (.returned (.val (.word (1 : BitVec 64))))) (emptyLocalsHOLFinite s) _ :=
    StatementRun.iteYes (costedExpression_events s _ _ neGuard1) (by decide) limb1Yes
  have rest1 : StatementRun s (.seq (u256LtLimb 1)
      (.seq u256LtFinal (.return (.const (0 : BitVec 64)))))
      (some (.returned (.val (.word (1 : BitVec 64))))) (emptyLocalsHOLFinite s) _ :=
    StatementRun.seqStop (second := _) (by simp) limb1
  have rest2 : StatementRun s (.seq (u256LtLimb 2) (.seq (u256LtLimb 1)
      (.seq u256LtFinal (.return (.const (0 : BitVec 64))))))
      (some (.returned (.val (.word (1 : BitVec 64))))) (emptyLocalsHOLFinite s) _ :=
    StatementRun.seqNext skip2 rest1
  rw [source_u256Lt_body]
  exact ⟨_, StatementRun.seqNext skip3 rest2⟩

#print axioms u256Lt_run_limb1_less

/-- Final-limb-less execution when limbs 3, 2 and 1 are equal. -/
theorem u256Lt_run_limb0_less (s : PanSemStateFiniteExact 64 F)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (hA : s.locals.lookup (ofString "a") =
      some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]))
    (hB : s.locals.lookup (ofString "b") =
      some (.rStruct [.val (.word b0), .val (.word b1), .val (.word b2), .val (.word b3)]))
    (h3 : a3 = b3) (h2 : a2 = b2) (h1 : a1 = b1) (hlt : a0 < b0) :
    ∃ events, StatementRun s (sourceFunctionBody Guest.guestFn_u256_lt)
      (some (.returned (.val (.word (1 : BitVec 64)))))
      (emptyLocalsHOLFinite s) events := by
  classical
  have ret0 : StatementRun s (.return (.const (0 : BitVec 64)))
      (some (.returned (.val (.word (0 : BitVec 64))))) (emptyLocalsHOLFinite s)
      (.statement :: (expressionEvents s (.const (0 : BitVec 64)) ++
        [.copy (flattenHOL (.val (.word (0 : BitVec 64)))).length])) :=
    StatementRun.returnValue (expression := .const (0 : BitVec 64))
      (costedExpression_events s _ _ (by simp [expressionValue, evalHOLExact]))
      (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])
  have ret1 : StatementRun s (.return (.const (1 : BitVec 64)))
      (some (.returned (.val (.word (1 : BitVec 64))))) (emptyLocalsHOLFinite s)
      (.statement :: (expressionEvents s (.const (1 : BitVec 64)) ++
        [.copy (flattenHOL (.val (.word (1 : BitVec 64)))).length])) :=
    StatementRun.returnValue (expression := .const (1 : BitVec 64))
      (costedExpression_events s _ _ (by simp [expressionValue, evalHOLExact]))
      (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])
  have ha3 := eval_rfield_four_three s (ofString "a") a0 a1 a2 a3 hA
  have hb3 := eval_rfield_four_three s (ofString "b") b0 b1 b2 b3 hB
  have skip3 : StatementRun s (u256LtLimb 3) none s
      (.statement :: (expressionEvents s _ ++ [.statement])) :=
    StatementRun.iteNo (costedExpression_events s _ _
      (eval_cmp_word_ne_false s _ _ a3 b3 ha3 hb3 h3)) (StatementRun.skip s)
  have ha2 := eval_rfield_four_two s (ofString "a") a0 a1 a2 a3 hA
  have hb2 := eval_rfield_four_two s (ofString "b") b0 b1 b2 b3 hB
  have skip2 : StatementRun s (u256LtLimb 2) none s
      (.statement :: (expressionEvents s _ ++ [.statement])) :=
    StatementRun.iteNo (costedExpression_events s _ _
      (eval_cmp_word_ne_false s _ _ a2 b2 ha2 hb2 h2)) (StatementRun.skip s)
  have ha1 := eval_rfield_four_one s (ofString "a") a0 a1 a2 a3 hA
  have hb1 := eval_rfield_four_one s (ofString "b") b0 b1 b2 b3 hB
  have skip1 : StatementRun s (u256LtLimb 1) none s
      (.statement :: (expressionEvents s _ ++ [.statement])) :=
    StatementRun.iteNo (costedExpression_events s _ _
      (eval_cmp_word_ne_false s _ _ a1 b1 ha1 hb1 h1)) (StatementRun.skip s)
  have ha0 := eval_rfield_four_zero s (ofString "a") a0 a1 a2 a3 hA
  have hb0 := eval_rfield_four_zero s (ofString "b") b0 b1 b2 b3 hB
  have ltGuard0 := eval_cmp_word_lt_true s _ _ a0 b0 ha0 hb0 hlt
  have finalRun : StatementRun s u256LtFinal
      (some (.returned (.val (.word (1 : BitVec 64))))) (emptyLocalsHOLFinite s) _ :=
    StatementRun.iteYes (costedExpression_events s _ _ ltGuard0) (by decide) ret1
  have finalSeq : StatementRun s (.seq u256LtFinal (.return (.const (0 : BitVec 64))))
      (some (.returned (.val (.word (1 : BitVec 64))))) (emptyLocalsHOLFinite s) _ :=
    StatementRun.seqStop (second := .return (.const (0 : BitVec 64))) (by simp) finalRun
  have rest1 : StatementRun s (.seq (u256LtLimb 1)
      (.seq u256LtFinal (.return (.const (0 : BitVec 64)))))
      (some (.returned (.val (.word (1 : BitVec 64))))) (emptyLocalsHOLFinite s) _ :=
    StatementRun.seqNext skip1 finalSeq
  have rest2 : StatementRun s (.seq (u256LtLimb 2) (.seq (u256LtLimb 1)
      (.seq u256LtFinal (.return (.const (0 : BitVec 64))))))
      (some (.returned (.val (.word (1 : BitVec 64))))) (emptyLocalsHOLFinite s) _ :=
    StatementRun.seqNext skip2 rest1
  rw [source_u256Lt_body]
  exact ⟨_, StatementRun.seqNext skip3 rest2⟩

#print axioms u256Lt_run_limb0_less

/-- A non-final limb whose words differ but where `a` is not lower returns zero. -/
theorem u256Lt_limb_greater_run (s : PanSemStateFiniteExact 64 F) (index : Nat)
    (a b : BitVec 64)
    (hA : expressionValue s (.rfield index (.var VarKind.local (ofString "a"))) =
      some (.val (.word a)))
    (hB : expressionValue s (.rfield index (.var VarKind.local (ofString "b"))) =
      some (.val (.word b)))
    (hne : a ≠ b) (hnotlt : ¬ a < b) :
    ∃ events, StatementRun s (u256LtLimb index)
      (some (.returned (.val (.word (0 : BitVec 64)))))
      (emptyLocalsHOLFinite s) events := by
  classical
  have neGuard := eval_cmp_word_ne_true s _ _ a b hA hB hne
  have ltValue := eval_cmp_word_true s _ _ a b hA hB
  have ltGuard : expressionValue s
      (.cmp Cmp.lower (.rfield index (.var VarKind.local (ofString "a")))
        (.rfield index (.var VarKind.local (ofString "b")))) =
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
      (.ite (.cmp Cmp.lower (.rfield index (.var VarKind.local (ofString "a")))
          (.rfield index (.var VarKind.local (ofString "b"))))
        (.return (.const (1 : BitVec 64))) .skip) none s
      (.statement :: (expressionEvents s _ ++ [.statement])) :=
    StatementRun.iteNo (costedExpression_events s _ _ ltGuard) (StatementRun.skip s)
  have yes : StatementRun s
      (.seq (.ite (.cmp Cmp.lower (.rfield index (.var VarKind.local (ofString "a")))
            (.rfield index (.var VarKind.local (ofString "b"))))
          (.return (.const (1 : BitVec 64))) .skip)
        (.return (.const (0 : BitVec 64))))
      (some (.returned (.val (.word (0 : BitVec 64))))) (emptyLocalsHOLFinite s) _ :=
    StatementRun.seqNext lowerIte ret0
  exact ⟨_, StatementRun.iteYes (costedExpression_events s _ _ neGuard) (by decide) yes⟩

/-- Limb-2-greater execution when the top limbs are equal. -/
theorem u256Lt_run_limb2_greater (s : PanSemStateFiniteExact 64 F)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (hA : s.locals.lookup (ofString "a") =
      some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]))
    (hB : s.locals.lookup (ofString "b") =
      some (.rStruct [.val (.word b0), .val (.word b1), .val (.word b2), .val (.word b3)]))
    (h3 : a3 = b3) (hne : a2 ≠ b2) (hnotlt : ¬ a2 < b2) :
    ∃ events, StatementRun s (sourceFunctionBody Guest.guestFn_u256_lt)
      (some (.returned (.val (.word (0 : BitVec 64)))))
      (emptyLocalsHOLFinite s) events := by
  classical
  have ha3 := eval_rfield_four_three s (ofString "a") a0 a1 a2 a3 hA
  have hb3 := eval_rfield_four_three s (ofString "b") b0 b1 b2 b3 hB
  have skip3 : StatementRun s (u256LtLimb 3) none s
      (.statement :: (expressionEvents s _ ++ [.statement])) :=
    StatementRun.iteNo (costedExpression_events s _ _
      (eval_cmp_word_ne_false s _ _ a3 b3 ha3 hb3 h3)) (StatementRun.skip s)
  have ha2 := eval_rfield_four_two s (ofString "a") a0 a1 a2 a3 hA
  have hb2 := eval_rfield_four_two s (ofString "b") b0 b1 b2 b3 hB
  have limb2 := u256Lt_limb_greater_run s 2 a2 b2 ha2 hb2 hne hnotlt
  obtain ⟨_, limb2Run⟩ := limb2
  have rest : StatementRun s (.seq (u256LtLimb 2) (.seq (u256LtLimb 1)
      (.seq u256LtFinal (.return (.const (0 : BitVec 64))))))
      (some (.returned (.val (.word (0 : BitVec 64))))) (emptyLocalsHOLFinite s) _ :=
    StatementRun.seqStop (second := _) (by simp) limb2Run
  rw [source_u256Lt_body]
  exact ⟨_, StatementRun.seqNext skip3 rest⟩

#print axioms u256Lt_limb_greater_run
#print axioms u256Lt_run_limb2_greater

#print axioms u256Lt_run_limb3_less
end InitECandidate.Runtime.FineCost
