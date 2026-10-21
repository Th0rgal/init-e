import ActualCandidateLoopGuardCost

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 1000000

/-- Actual candidate loop-body store address `vals + i * 8` costs 132 source
units at one-word locals. -/
theorem sourcePrice_body_address {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hv : valueInfo s.locals (ofString "vals") = some (ShapeHOL.one, 1))
    (hi : valueInfo s.locals (ofString "i") = some (ShapeHOL.one, 1)) :
    sourcePrice s (.op .add [.var .local (ofString "vals"),
      .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]]) = 132 := by
  simp [sourcePrice, sourcePrices, exprPrices, exprListPrices, cexpHeads, hv, hi]

/-- Actual candidate loop-body stored value `i + 2` costs 61 source units. -/
theorem sourcePrice_body_value {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hi : valueInfo s.locals (ofString "i") = some (ShapeHOL.one, 1)) :
    sourcePrice s (.op .add [.var .local (ofString "i"),
      .const (BitVec.ofNat 64 2)]) = 61 := by
  simp [sourcePrice, sourcePrices, exprPrices, exprListPrices, cexpHeads, hi]

/-- Actual candidate loop-body increment `i + 1` costs 61 source units. -/
theorem sourcePrice_body_increment {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hi : valueInfo s.locals (ofString "i") = some (ShapeHOL.one, 1)) :
    sourcePrice s (.op .add [.var .local (ofString "i"),
      .const (BitVec.ofNat 64 1)]) = 61 := by
  simp [sourcePrice, sourcePrices, exprPrices, exprListPrices, cexpHeads, hi]

end BoundedTableExperiment

#print axioms BoundedTableExperiment.sourcePrice_body_address
#print axioms BoundedTableExperiment.sourcePrice_body_value
#print axioms BoundedTableExperiment.sourcePrice_body_increment

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Trace cost bound for the loop-body store address. -/
theorem body_address_score_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    {value : Option (ValueHOL 64)} {events : List WorkEvent} (coeff : Work)
    (run : CostedExpressionRun s (.op .add [.var .local (ofString "vals"),
      .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]]) value events)
    (hv : valueInfo s.locals (ofString "vals") = some (ShapeHOL.one, 1))
    (hi : valueInfo s.locals (ofString "i") = some (ShapeHOL.one, 1)) :
    coeff.score (executionWork events) ≤ coeff.nativeCost * 132 := by
  rw [run.events_eq]
  change expressionCost coeff s (.op .add [.var .local (ofString "vals"),
    .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]]) ≤
    coeff.nativeCost * 132
  rw [expressionCost_eq, sourcePrice_body_address s hv hi]

/-- Trace cost bound for the loop-body stored value. -/
theorem body_value_score_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    {value : Option (ValueHOL 64)} {events : List WorkEvent} (coeff : Work)
    (run : CostedExpressionRun s (.op .add [.var .local (ofString "i"),
      .const (BitVec.ofNat 64 2)]) value events)
    (hi : valueInfo s.locals (ofString "i") = some (ShapeHOL.one, 1)) :
    coeff.score (executionWork events) ≤ coeff.nativeCost * 61 := by
  rw [run.events_eq]
  change expressionCost coeff s (.op .add [.var .local (ofString "i"),
    .const (BitVec.ofNat 64 2)]) ≤ coeff.nativeCost * 61
  rw [expressionCost_eq, sourcePrice_body_value s hi]

/-- Trace cost bound for the loop-body increment value. -/
theorem body_increment_score_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    {value : Option (ValueHOL 64)} {events : List WorkEvent} (coeff : Work)
    (run : CostedExpressionRun s (.op .add [.var .local (ofString "i"),
      .const (BitVec.ofNat 64 1)]) value events)
    (hi : valueInfo s.locals (ofString "i") = some (ShapeHOL.one, 1)) :
    coeff.score (executionWork events) ≤ coeff.nativeCost * 61 := by
  rw [run.events_eq]
  change expressionCost coeff s (.op .add [.var .local (ofString "i"),
    .const (BitVec.ofNat 64 1)]) ≤ coeff.nativeCost * 61
  rw [expressionCost_eq, sourcePrice_body_increment s hi]

end BoundedTableExperiment

#print axioms BoundedTableExperiment.body_address_score_bound
#print axioms BoundedTableExperiment.body_value_score_bound
#print axioms BoundedTableExperiment.body_increment_score_bound

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The stored loop-body value `i + 2`, whenever it evaluates, is a word. -/
theorem body_value_word {F : Type} (t : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64)
    (h : expressionValue t (.op .add [.var .local (ofString "i"),
      .const (BitVec.ofNat 64 2)]) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  simp only [expressionValue, evalHOLExact, evalListHOLExact] at h
  cases hl : t.locals.lookup (ofString "i") with
  | none => simp [hl] at h
  | some val =>
      simp [hl] at h
      rcases h with ⟨_, a, _, hv⟩
      exact ⟨a, hv.symm⟩

/-- The increment value `i + 1`, whenever it evaluates, is a word. -/
theorem body_increment_word {F : Type} (t : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64)
    (h : expressionValue t (.op .add [.var .local (ofString "i"),
      .const (BitVec.ofNat 64 1)]) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  simp only [expressionValue, evalHOLExact, evalListHOLExact] at h
  cases hl : t.locals.lookup (ofString "i") with
  | none => simp [hl] at h
  | some val =>
      simp [hl] at h
      rcases h with ⟨_, a, _, hv⟩
      exact ⟨a, hv.symm⟩

/-- A word value flattens to exactly one word. -/
theorem word_value_flatten (w : BitVec 64) :
    (flattenHOL (ValueHOL.val (.word w))).length = 1 := by
  simp [flattenHOL]

end BoundedTableExperiment

#print axioms BoundedTableExperiment.body_value_word
#print axioms BoundedTableExperiment.body_increment_word
#print axioms BoundedTableExperiment.word_value_flatten
