import InitECandidate.Runtime.GuestCostU256Add
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {F : Type}

/-- Word comparison of two evaluated words, true case. -/
theorem eval_cmp_word_true (s : PanSemStateFiniteExact 64 F)
    (left right : ExpHOL 64) (a b : BitVec 64)
    (hLeft : expressionValue s left = some (.val (.word a)))
    (hRight : expressionValue s right = some (.val (.word b))) :
    expressionValue s (.cmp Cmp.lower left right) =
      some (.val (.word (if a < b then 1 else 0))) := by
  classical
  unfold expressionValue
  have hL := hLeft
  have hR := hRight
  simp only [expressionValue] at hL hR
  simp [evalHOLExact, hL, hR, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

/-- Word inequality of two evaluated words, true case. -/
theorem eval_cmp_word_ne_true (s : PanSemStateFiniteExact 64 F)
    (left right : ExpHOL 64) (a b : BitVec 64)
    (hLeft : expressionValue s left = some (.val (.word a)))
    (hRight : expressionValue s right = some (.val (.word b)))
    (hne : a ≠ b) :
    expressionValue s (.cmp Cmp.notEqual left right) = some (.val (.word 1)) := by
  classical
  unfold expressionValue
  have hL := hLeft
  have hR := hRight
  simp only [expressionValue] at hL hR
  simp [evalHOLExact, hL, hR, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]

/-- Word comparison of two evaluated words, true case at value one. -/
theorem eval_cmp_word_lt_true (s : PanSemStateFiniteExact 64 F)
    (left right : ExpHOL 64) (a b : BitVec 64)
    (hLeft : expressionValue s left = some (.val (.word a)))
    (hRight : expressionValue s right = some (.val (.word b)))
    (hlt : a < b) :
    expressionValue s (.cmp Cmp.lower left right) = some (.val (.word 1)) := by
  rw [eval_cmp_word_true s left right a b hLeft hRight]
  simp [hlt]

/-- Word inequality of two evaluated equal words is zero. -/
theorem eval_cmp_word_ne_false (s : PanSemStateFiniteExact 64 F)
    (left right : ExpHOL 64) (a b : BitVec 64)
    (hLeft : expressionValue s left = some (.val (.word a)))
    (hRight : expressionValue s right = some (.val (.word b)))
    (heq : a = b) :
    expressionValue s (.cmp Cmp.notEqual left right) = some (.val (.word 0)) := by
  classical
  unfold expressionValue
  have hL := hLeft
  have hR := hRight
  simp only [expressionValue] at hL hR
  simp [evalHOLExact, hL, hR, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, heq]

#print axioms eval_cmp_word_ne_false

#print axioms eval_cmp_word_true
#print axioms eval_cmp_word_ne_true
#print axioms eval_cmp_word_lt_true
end InitECandidate.Runtime.FineCost
