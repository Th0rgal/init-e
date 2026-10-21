import ActualCandidateLoopBodyPrice
import ActualStoreWorkDecomposition

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- Fixed work bound of the body store `st vals + i*8, i + 2`. -/
def bodyStoreBound (coeff : Work) : Nat :=
  coeff.score WorkEvent.statement.units +
    (coeff.score (WorkEvent.memory 1).units +
      (coeff.score (WorkEvent.cost (storeOverhead 1)).units +
        (coeff.nativeCost * 132 + coeff.nativeCost * 61)))

/-- Fixed work bound of the body assignment `i = i + 1`. -/
def bodyAssignBound (coeff : Work) : Nat :=
  coeff.score WorkEvent.statement.units +
    (coeff.score (WorkEvent.copy 1).units + coeff.nativeCost * 61)

/-- Any actual run of the body store costs at most the fixed store bound. -/
theorem store_run_body_bound {F : Type} {fn : MlS}
    {t middle : PanSemStateFiniteExact 64 F}
    {result : Option (PanSemResultExact 64)} {events : List WorkEvent}
    (coeff : Work)
    (run : StatementRun fn t
      (.store (.op .add [.var .local (ofString "vals"),
          .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]])
        (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 2)]))
      result middle events)
    (hv : valueInfo t.locals (ofString "vals") = some (ShapeHOL.one, 1))
    (hi : valueInfo t.locals (ofString "i") = some (ShapeHOL.one, 1)) :
    coeff.score (executionWork events) ≤ bodyStoreBound coeff := by
  cases run with
  | storeValue dst src write =>
      have hha := body_address_score_bound coeff dst hv hi
      have hhv := body_value_score_bound coeff src hi
      obtain ⟨w, hw⟩ := body_value_word t _ src.sound
      subst hw
      simp only [word_value_flatten]
      rw [executionWork_store_events]
      simp only [bodyStoreBound]
      omega
  | storeRejected dst src write =>
      have hha := body_address_score_bound coeff dst hv hi
      have hhv := body_value_score_bound coeff src hi
      obtain ⟨w, hw⟩ := body_value_word t _ src.sound
      subst hw
      simp only [word_value_flatten]
      rw [executionWork_store_events]
      simp only [bodyStoreBound]
      omega
  | storeSourceFailure dst src =>
      have hha := body_address_score_bound coeff dst hv hi
      have hhv := body_value_score_bound coeff src hi
      simp only [executionWork_score_cons, executionWork_score_append]
      simp only [bodyStoreBound]
      omega
  | storeAddressFailure dst =>
      have hha := body_address_score_bound coeff dst hv hi
      simp only [executionWork_score_cons]
      simp only [bodyStoreBound]
      omega
  | storeInvalidAddress dst invalid =>
      have hha := body_address_score_bound coeff dst hv hi
      simp only [executionWork_score_cons]
      simp only [bodyStoreBound]
      omega

end BoundedTableExperiment

#print axioms BoundedTableExperiment.store_run_body_bound

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Any actual run of the body assignment costs at most the fixed assign
bound. -/
theorem assign_run_body_bound {F : Type} {fn : MlS}
    {t middle : PanSemStateFiniteExact 64 F}
    {result : Option (PanSemResultExact 64)} {events : List WorkEvent}
    (coeff : Work)
    (run : StatementRun fn t
      (.assign .local (ofString "i")
        (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))
      result middle events)
    (hi : valueInfo t.locals (ofString "i") = some (ShapeHOL.one, 1)) :
    coeff.score (executionWork events) ≤ bodyAssignBound coeff := by
  cases run with
  | assignValue expr valid =>
      have hvi := body_increment_score_bound coeff expr hi
      obtain ⟨w, hw⟩ := body_increment_word t _ expr.sound
      subst hw
      simp only [word_value_flatten, globalEvents, List.append_nil]
      rw [executionWork_assign_events]
      simp only [bodyAssignBound]
      omega
  | assignInvalid expr invalid =>
      have hvi := body_increment_score_bound coeff expr hi
      simp only [executionWork_score_cons]
      simp only [bodyAssignBound]
      omega
  | assignFailure expr =>
      have hvi := body_increment_score_bound coeff expr hi
      simp only [executionWork_score_cons]
      simp only [bodyAssignBound]
      omega

end BoundedTableExperiment

#print axioms BoundedTableExperiment.assign_run_body_bound

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A store run never changes the locals. -/
theorem store_run_locals_eq {F : Type} {fn : MlS}
    {t middle : PanSemStateFiniteExact 64 F} {destination source : ExpHOL 64}
    {result : Option (PanSemResultExact 64)} {events : List WorkEvent}
    (run : StatementRun fn t (.store destination source) result middle events) :
    middle.locals = t.locals := by
  cases run with
  | storeValue dst src write => rfl
  | storeRejected dst src write => rfl
  | storeSourceFailure dst src => rfl
  | storeAddressFailure dst => rfl
  | storeInvalidAddress dst invalid => rfl

/-- Any actual run of the candidate loop body `st vals + i*8, i+2; i = i+1`
costs at most the fixed body bound. -/
theorem body_run_bound {F : Type} {fn : MlS}
    {t middle : PanSemStateFiniteExact 64 F}
    {result : Option (PanSemResultExact 64)} {events : List WorkEvent}
    (coeff : Work)
    (run : StatementRun fn t
      (.seq (.store (.op .add [.var .local (ofString "vals"),
          .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]])
        (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 2)]))
        (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))
      result middle events)
    (hv : valueInfo t.locals (ofString "vals") = some (ShapeHOL.one, 1))
    (hi : valueInfo t.locals (ofString "i") = some (ShapeHOL.one, 1)) :
    coeff.score (executionWork events) ≤ bodyStoreBound coeff + bodyAssignBound coeff := by
  cases run with
  | seqNext one two =>
      have h1 := store_run_body_bound coeff one hv hi
      have hl := store_run_locals_eq one
      have h2 := assign_run_body_bound coeff two (by rw [hl]; exact hi)
      rw [executionWork_score_append]
      omega
  | seqStop terminal one =>
      have h1 := store_run_body_bound coeff one hv hi
      omega

end BoundedTableExperiment

#print axioms BoundedTableExperiment.body_run_bound

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The concrete candidate loop `while i < cap { st vals + i*8, i+2;
i = i+1 }`: at most 480 iterations and fully bounded work, with the body bound
discharged from the actual store/assignment runs. -/
theorem candidate_loop_body_bounded_cost {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {events : List WorkEvent} {n : Nat}
    {rank : PanSemStateFiniteExact 64 F → Nat}
    (count : WhileCount fn
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "cap")))
      (.seq (.store (.op .add [.var .local (ofString "vals"),
          .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]])
        (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 2)]))
        (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))
      s r post events n)
    (start : rank s < 480)
    (step : ∀ (t middle : PanSemStateFiniteExact 64 F)
      (result : Option (PanSemResultExact 64)) (bodyEvents : List WorkEvent),
      StatementRun fn (decClockHOLFinite t)
        (.seq (.store (.op .add [.var .local (ofString "vals"),
            .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]])
          (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 2)]))
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))
        result middle bodyEvents →
        rank t < rank middle ∧ rank middle < 480)
    (coeff : Work)
    (hshape : ∀ (t : PanSemStateFiniteExact 64 F)
      (value : Option (ValueHOL 64)) (guardEvents : List WorkEvent),
      CostedExpressionRun t
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "cap")))
        value guardEvents →
      valueInfo t.locals (ofString "i") = some (ShapeHOL.one, 1) ∧
        valueInfo t.locals (ofString "cap") = some (ShapeHOL.one, 1))
    (hbodyShape : ∀ (v : PanSemStateFiniteExact 64 F),
      valueInfo v.locals (ofString "vals") = some (ShapeHOL.one, 1) ∧
        valueInfo v.locals (ofString "i") = some (ShapeHOL.one, 1)) :
    n ≤ 480 ∧ coeff.score (executionWork events) ≤
      480 * (((coeff.score WorkEvent.statement.units +
        coeff.score (WorkEvent.cost (whileOverhead + loopMoves fn)).units) +
        coeff.nativeCost * 98) + (bodyStoreBound coeff + bodyAssignBound coeff)) +
        (coeff.score WorkEvent.statement.units +
          ((coeff.score WorkEvent.statement.units +
            coeff.score (WorkEvent.cost (whileOverhead + loopMoves fn)).units) +
            coeff.nativeCost * 98)) := by
  refine candidate_loop_selfterminated_cost count start step coeff
    (bodyStoreBound coeff + bodyAssignBound coeff) hshape ?_
  intro t u v result bodyEvents one
  exact body_run_bound coeff one (hbodyShape v).1 (hbodyShape v).2

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidate_loop_body_bounded_cost

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- One-word local values give one-word source prices. -/
theorem valueInfo_of_word {F : Type} {s : PanSemStateFiniteExact 64 F} {name : MlS}
    {w : BitVec 64}
    (h : s.locals.lookup name = some (.val (.word w))) :
    valueInfo s.locals name = some (ShapeHOL.one, 1) := by
  simp [valueInfo, h, shapeOfHOLExact, flattenHOL]

/-- The concrete candidate loop `while i < cap { ... }` with one-word locals:
at most 480 iterations and fully bounded work, with guard and body shape facts
derived from actual word lookups. -/
theorem candidate_loop_body_bounded_cost_of_words {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {events : List WorkEvent} {n : Nat}
    {rank : PanSemStateFiniteExact 64 F → Nat}
    (count : WhileCount fn
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "cap")))
      (.seq (.store (.op .add [.var .local (ofString "vals"),
          .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]])
        (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 2)]))
        (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))
      s r post events n)
    (start : rank s < 480)
    (step : ∀ (t middle : PanSemStateFiniteExact 64 F)
      (result : Option (PanSemResultExact 64)) (bodyEvents : List WorkEvent),
      StatementRun fn (decClockHOLFinite t)
        (.seq (.store (.op .add [.var .local (ofString "vals"),
            .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]])
          (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 2)]))
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))
        result middle bodyEvents →
        rank t < rank middle ∧ rank middle < 480)
    (coeff : Work)
    (hguardWords : ∀ (t : PanSemStateFiniteExact 64 F)
      (value : Option (ValueHOL 64)) (guardEvents : List WorkEvent),
      CostedExpressionRun t
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "cap")))
        value guardEvents →
      (∃ wi, t.locals.lookup (ofString "i") = some (.val (.word wi))) ∧
        (∃ wc, t.locals.lookup (ofString "cap") = some (.val (.word wc))))
    (hbodyWords : ∀ (v : PanSemStateFiniteExact 64 F),
      (∃ wv, v.locals.lookup (ofString "vals") = some (.val (.word wv))) ∧
        (∃ wi, v.locals.lookup (ofString "i") = some (.val (.word wi)))) :
    n ≤ 480 ∧ coeff.score (executionWork events) ≤
      480 * (((coeff.score WorkEvent.statement.units +
        coeff.score (WorkEvent.cost (whileOverhead + loopMoves fn)).units) +
        coeff.nativeCost * 98) + (bodyStoreBound coeff + bodyAssignBound coeff)) +
        (coeff.score WorkEvent.statement.units +
          ((coeff.score WorkEvent.statement.units +
            coeff.score (WorkEvent.cost (whileOverhead + loopMoves fn)).units) +
            coeff.nativeCost * 98)) := by
  refine candidate_loop_body_bounded_cost count start step coeff ?_ ?_
  · intro t value guardEvents run
    obtain ⟨⟨wi, hiw⟩, ⟨wc, hcw⟩⟩ := hguardWords t value guardEvents run
    exact ⟨valueInfo_of_word hiw, valueInfo_of_word hcw⟩
  · intro v
    obtain ⟨⟨wv, hvw⟩, ⟨wi, hiw⟩⟩ := hbodyWords v
    exact ⟨valueInfo_of_word hvw, valueInfo_of_word hiw⟩

end BoundedTableExperiment

#print axioms BoundedTableExperiment.valueInfo_of_word
#print axioms BoundedTableExperiment.candidate_loop_body_bounded_cost_of_words
