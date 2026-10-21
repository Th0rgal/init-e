import ActualCandidateLoopGuardCost
import ActualCandidateLoopBodyBound
import ActualWhileBoundedStep

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Rank of the candidate counter loop: the numeric value of `i` when it is a
word, and zero otherwise. -/
noncomputable def counterRank {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup (ofString "i") with
  | some (.val (.word w)) => w.toNat
  | _ => 0

/-- A word counter rank is exactly that word's numeric value. -/
theorem counterRank_word {F : Type} {s : PanSemStateFiniteExact 64 F} {w : BitVec 64}
    (h : s.locals.lookup (ofString "i") = some (.val (.word w))) :
    counterRank s = w.toNat := by
  simp [counterRank, h]

/-- A nonzero `i < cap` guard at one-word locals really means `i < cap`. -/
theorem guard_lower_word {F : Type} {t : PanSemStateFiniteExact 64 F}
    {value : ValueHOL 64} {a b : BitVec 64}
    (hi : t.locals.lookup (ofString "i") = some (.val (.word a)))
    (hc : t.locals.lookup (ofString "cap") = some (.val (.word b)))
    (h : expressionValue t
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "cap"))) =
        some value)
    (hne : value ≠ .val (.word 0)) :
    a < b := by
  simp only [expressionValue, evalHOLExact, hi, hc,
    Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def] at h
  have hv : value =
      .val (.word (if decide (a.toNat < b.toNat) = true then 1 else 0)) := by
    simpa using h.symm
  rw [hv] at hne
  by_cases hab : a.toNat < b.toNat
  · simpa [BitVec.lt_def] using hab
  · simp [hab] at hne

end BoundedTableExperiment

#print axioms BoundedTableExperiment.counterRank_word
#print axioms BoundedTableExperiment.guard_lower_word

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Word-valued form of the guard comparison. -/
theorem guard_lower_word_bit {F : Type} {t : PanSemStateFiniteExact 64 F}
    {value a b : BitVec 64}
    (hi : t.locals.lookup (ofString "i") = some (.val (.word a)))
    (hc : t.locals.lookup (ofString "cap") = some (.val (.word b)))
    (h : expressionValue t
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "cap"))) =
        some (.val (.word value)))
    (hne : value ≠ 0) :
    a < b :=
  guard_lower_word hi hc h (by simpa using hne)

/-- Guard-aware iteration bound for the candidate counter loop `while i < cap`:
if every state has one-word `i` and the initial `cap` word `b` is `< 480`, and
each continuing body run increments the counter rank, then the loop runs at
most `b + 1` iterations. -/
theorem whileCount_counter_le_cap {F : Type} {fn : MlS}
    {body : ProgHOL 64} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {events : List WorkEvent} {n : Nat}
    {b : BitVec 64}
    (count : WhileCount fn
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "cap")))
      body s r post events n)
    (hcap : ∀ (t : PanSemStateFiniteExact 64 F),
      t.locals.lookup (ofString "cap") = some (.val (.word b)))
    (hword : ∀ (t : PanSemStateFiniteExact 64 F),
      ∃ a : BitVec 64, t.locals.lookup (ofString "i") = some (.val (.word a)))
    (step : ∀ (t middle : PanSemStateFiniteExact 64 F)
      (result : Option (PanSemResultExact 64)) (bodyEvents : List WorkEvent),
      StatementRun fn (decClockHOLFinite t) body result middle bodyEvents →
        (result = none ∨ result = some .continue) →
        counterRank middle = counterRank t + 1)
    (start : counterRank s ≤ b.toNat) :
    counterRank s + n ≤ b.toNat + 1 := by
  induction count with
  | stop guard => omega
  | next guard nonzero clock one rest ih =>
      obtain ⟨a, ha⟩ := hword _
      have hlt := guard_lower_word_bit ha (hcap _) guard.sound nonzero
      have hnat : a.toNat < b.toNat := by simpa [BitVec.lt_def] using hlt
      have hidx := counterRank_word ha
      have hinc := step _ _ _ _ one (Or.inl rfl)
      have hrest := ih (by rw [hinc, hidx]; omega)
      rw [hinc, hidx] at hrest
      omega
  | breakLoop guard nonzero one => omega
  | continueLoop guard nonzero clock one rest ih =>
      obtain ⟨a, ha⟩ := hword _
      have hlt := guard_lower_word_bit ha (hcap _) guard.sound nonzero
      have hnat : a.toNat < b.toNat := by simpa [BitVec.lt_def] using hlt
      have hidx := counterRank_word ha
      have hinc := step _ _ _ _ one (Or.inr rfl)
      have hrest := ih (by rw [hinc, hidx]; omega)
      rw [hinc, hidx] at hrest
      omega
  | timeout guard nonzero clock => omega
  | missingGuard guard => omega
  | invalidGuard guard notWord => omega
  | propagate guard nonzero clock notBreak notContinue one => omega

end BoundedTableExperiment

#print axioms BoundedTableExperiment.whileCount_counter_le_cap

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every continuing run of the actual body `st vals + i*8, i+2; i = i+1`
increments the counter rank (below 480). -/
theorem body_counterRank_step {F : Type} {fn : MlS}
    {t middle : PanSemStateFiniteExact 64 F}
    {result : Option (PanSemResultExact 64)} {bodyEvents : List WorkEvent}
    {wi : BitVec 64}
    (run : StatementRun fn (decClockHOLFinite t)
      (.seq (.store (.op .add [.var .local (ofString "vals"),
          .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]])
        (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 2)]))
        (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))
      result middle bodyEvents)
    (hwi : t.locals.lookup (ofString "i") = some (.val (.word wi)))
    (hlt : wi.toNat < 480)
    (hcont : result = none ∨ result = some .continue) :
    counterRank middle = counterRank t + 1 := by
  have hidx := counterRank_word hwi
  cases run with
  | seqNext one two =>
      have hl := store_run_locals_eq one
      cases two with
      | assignValue expr valid =>
          obtain ⟨w, hw⟩ := body_increment_word _ _ expr.sound
          have hwi2 : (decClockHOLFinite t).locals.lookup (ofString "i") =
              some (.val (.word wi)) := by
            simp [decClockHOLFinite, hwi]
          have hs : w = wi + 1 := by
            have hsound := expr.sound
            rw [hw] at hsound
            simp [expressionValue, evalHOLExact, evalListHOLExact, hl, hwi2] at hsound
            have hop := hsound.2
            simp [wordOpHOL, wordOp, valueWord] at hop
            trace_state
            exact hop.symm
          rw [hw, hs]
          simp [counterRank, setKvarHOLFinite, setVarHOLFinite, hl, hwi, FUPDATE,
            HolFiniteMapExact.lookup_updateEq, bitvec_succ_toNat wi hlt]
      | assignInvalid expr invalid =>
          rcases hcont with h | h <;> simp at h
      | assignFailure expr =>
          rcases hcont with h | h <;> simp at h
  | seqStop terminal one =>
      rcases hcont with h | h
      · exact absurd h terminal
      · cases one <;> simp_all

end BoundedTableExperiment

#print axioms BoundedTableExperiment.body_counterRank_step

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- At one-word `i`/`cap`, the `i < cap` guard always evaluates to a word. -/
theorem guard_value_word {F : Type} {t : PanSemStateFiniteExact 64 F} {a b : BitVec 64}
    (hi : t.locals.lookup (ofString "i") = some (.val (.word a)))
    (hc : t.locals.lookup (ofString "cap") = some (.val (.word b))) :
    ∃ value : BitVec 64,
      expressionValue t
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "cap"))) =
          some (.val (.word value)) := by
  refine ⟨if decide (a.toNat < b.toNat) = true then 1 else 0, ?_⟩
  simp only [expressionValue, evalHOLExact, hi, hc,
    Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]

/-- Sharper capacity-init bound: with a well-formed guard (always a word), the
loop `while i < cap { st vals + i*8, i+2; i = i+1 }` runs at most `cap`
iterations. -/
theorem whileCount_counter_le_cap_strict {F : Type} {fn : MlS}
    {body : ProgHOL 64} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {events : List WorkEvent} {n : Nat}
    {b : BitVec 64}
    (count : WhileCount fn
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "cap")))
      body s r post events n)
    (hcap : ∀ (t : PanSemStateFiniteExact 64 F),
      t.locals.lookup (ofString "cap") = some (.val (.word b)))
    (hword : ∀ (t : PanSemStateFiniteExact 64 F),
      ∃ a : BitVec 64, t.locals.lookup (ofString "i") = some (.val (.word a)))
    (hguardWord : ∀ (t : PanSemStateFiniteExact 64 F) (value : Option (ValueHOL 64))
      (guardEvents : List WorkEvent),
      CostedExpressionRun t
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "cap")))
        value guardEvents →
      ∃ w : BitVec 64, value = some (.val (.word w)))
    (step : ∀ (t middle : PanSemStateFiniteExact 64 F)
      (result : Option (PanSemResultExact 64)) (bodyEvents : List WorkEvent),
      StatementRun fn (decClockHOLFinite t) body result middle bodyEvents →
        (result = none ∨ result = some .continue) →
        counterRank middle = counterRank t + 1)
    (start : counterRank s ≤ b.toNat) :
    counterRank s + n ≤ b.toNat := by
  induction count with
  | stop guard => omega
  | next guard nonzero clock one rest ih =>
      obtain ⟨a, ha⟩ := hword _
      have hlt := guard_lower_word_bit ha (hcap _) guard.sound nonzero
      have hnat : a.toNat < b.toNat := by simpa [BitVec.lt_def] using hlt
      have hidx := counterRank_word ha
      have hinc := step _ _ _ _ one (Or.inl rfl)
      have hrest := ih (by rw [hinc, hidx]; omega)
      rw [hinc, hidx] at hrest
      omega
  | breakLoop guard nonzero one =>
      obtain ⟨a, ha⟩ := hword _
      have hlt := guard_lower_word_bit ha (hcap _) guard.sound nonzero
      have hnat : a.toNat < b.toNat := by simpa [BitVec.lt_def] using hlt
      have hidx := counterRank_word ha
      omega
  | continueLoop guard nonzero clock one rest ih =>
      obtain ⟨a, ha⟩ := hword _
      have hlt := guard_lower_word_bit ha (hcap _) guard.sound nonzero
      have hnat : a.toNat < b.toNat := by simpa [BitVec.lt_def] using hlt
      have hidx := counterRank_word ha
      have hinc := step _ _ _ _ one (Or.inr rfl)
      have hrest := ih (by rw [hinc, hidx]; omega)
      rw [hinc, hidx] at hrest
      omega
  | timeout guard nonzero clock =>
      obtain ⟨a, ha⟩ := hword _
      have hlt := guard_lower_word_bit ha (hcap _) guard.sound nonzero
      have hnat : a.toNat < b.toNat := by simpa [BitVec.lt_def] using hlt
      have hidx := counterRank_word ha
      omega
  | missingGuard guard =>
      obtain ⟨w, hw⟩ := hguardWord _ _ _ guard
      simp at hw
  | invalidGuard guard notWord =>
      obtain ⟨w, hw⟩ := hguardWord _ _ _ guard
      exact absurd hw (notWord w)
  | propagate guard nonzero clock notBreak notContinue one =>
      obtain ⟨a, ha⟩ := hword _
      have hlt := guard_lower_word_bit ha (hcap _) guard.sound nonzero
      have hnat : a.toNat < b.toNat := by simpa [BitVec.lt_def] using hlt
      have hidx := counterRank_word ha
      omega

end BoundedTableExperiment

#print axioms BoundedTableExperiment.guard_value_word
#print axioms BoundedTableExperiment.whileCount_counter_le_cap_strict

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Capacity-init loop cost is linear in the actual cap: `n <= cap` and the
actual work is at most `cap * perIteration + base` for the frozen header loops
`while i < cap { st vals + i*8, i+2; i = i+1 }`. -/
theorem candidate_capacity_init_cost_linear {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {events : List WorkEvent} {n : Nat}
    {b : BitVec 64}
    (count : WhileCount fn
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "cap")))
      (.seq (.store (.op .add [.var .local (ofString "vals"),
          .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]])
        (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 2)]))
        (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))
      s r post events n)
    (hcap : ∀ (t : PanSemStateFiniteExact 64 F),
      t.locals.lookup (ofString "cap") = some (.val (.word b)))
    (hword : ∀ (t : PanSemStateFiniteExact 64 F),
      ∃ a : BitVec 64, t.locals.lookup (ofString "i") = some (.val (.word a)))
    (hvals : ∀ (t : PanSemStateFiniteExact 64 F),
      ∃ w : BitVec 64, t.locals.lookup (ofString "vals") = some (.val (.word w)))
    (hguardWord : ∀ (t : PanSemStateFiniteExact 64 F) (value : Option (ValueHOL 64))
      (guardEvents : List WorkEvent),
      CostedExpressionRun t
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "cap")))
        value guardEvents →
      ∃ w : BitVec 64, value = some (.val (.word w)))
    (step : ∀ (t middle : PanSemStateFiniteExact 64 F)
      (result : Option (PanSemResultExact 64)) (bodyEvents : List WorkEvent),
      StatementRun fn (decClockHOLFinite t)
        (.seq (.store (.op .add [.var .local (ofString "vals"),
            .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]])
          (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 2)]))
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))
        result middle bodyEvents →
        (result = none ∨ result = some .continue) →
        counterRank middle = counterRank t + 1)
    (start : counterRank s ≤ b.toNat)
    (coeff : Work) :
    n ≤ b.toNat ∧ coeff.score (executionWork events) ≤
      b.toNat * ((coeff.score WorkEvent.statement.units +
        coeff.score (WorkEvent.cost (whileOverhead + loopMoves fn)).units) +
        coeff.nativeCost * 98 + (bodyStoreBound coeff + bodyAssignBound coeff)) +
      (coeff.score WorkEvent.statement.units +
        ((coeff.score WorkEvent.statement.units +
          coeff.score (WorkEvent.cost (whileOverhead + loopMoves fn)).units) +
          coeff.nativeCost * 98)) := by
  have hshape : ∀ (t : PanSemStateFiniteExact 64 F) (value : Option (ValueHOL 64))
      (guardEvents : List WorkEvent),
      CostedExpressionRun t
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "cap")))
        value guardEvents →
      valueInfo t.locals (ofString "i") = some (ShapeHOL.one, 1) ∧
        valueInfo t.locals (ofString "cap") = some (ShapeHOL.one, 1) := by
    intro t value guardEvents run
    obtain ⟨a, ha⟩ := hword t
    have hv := valueInfo_of_word ha
    have hcv := valueInfo_of_word (hcap t)
    exact ⟨hv, hcv⟩
  have hbody : ∀ (t u v : PanSemStateFiniteExact 64 F)
      (result : Option (PanSemResultExact 64)) (bodyEvents : List WorkEvent),
      StatementRun fn v
        (.seq (.store (.op .add [.var .local (ofString "vals"),
            .panop .mul [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]])
          (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 2)]))
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))
        result u bodyEvents →
      coeff.score (executionWork bodyEvents) ≤
        bodyStoreBound coeff + bodyAssignBound coeff := by
    intro t u v result bodyEvents run
    obtain ⟨wv, hwv⟩ := hvals v
    obtain ⟨wi, hwi⟩ := hword v
    exact body_run_bound coeff run (valueInfo_of_word hwv) (valueInfo_of_word hwi)
  have hmissing : ∀ (t : PanSemStateFiniteExact 64 F) (value : Option (ValueHOL 64))
      (guardEvents : List WorkEvent),
      CostedExpressionRun t
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "cap")))
        value guardEvents →
      coeff.score (executionWork (WorkEvent.statement :: guardEvents)) ≤
        (coeff.score WorkEvent.statement.units +
          ((coeff.score WorkEvent.statement.units +
            coeff.score (WorkEvent.cost (whileOverhead + loopMoves fn)).units) +
            coeff.nativeCost * 98)) := by
    intro t value guardEvents run
    have hg := loop_guard_score_bound coeff run
      (valueInfo_of_word (hword t).choose_spec)
      (valueInfo_of_word (hcap t))
    rw [executionWork_score_cons]
    omega
  have hterminal : (coeff.score WorkEvent.statement.units +
      coeff.score (WorkEvent.cost (whileOverhead + loopMoves fn)).units) +
      coeff.nativeCost * 98 ≤
      (coeff.score WorkEvent.statement.units +
        ((coeff.score WorkEvent.statement.units +
          coeff.score (WorkEvent.cost (whileOverhead + loopMoves fn)).units) +
          coeff.nativeCost * 98)) := by
    omega
  have hiter := candidate_loop_uniform_cost_literal count coeff
    (bodyStoreBound coeff + bodyAssignBound coeff)
    (coeff.score WorkEvent.statement.units +
      ((coeff.score WorkEvent.statement.units +
        coeff.score (WorkEvent.cost (whileOverhead + loopMoves fn)).units) +
        coeff.nativeCost * 98)) hshape hbody hmissing hterminal
  have hcount := whileCount_counter_le_cap_strict count hcap hword hguardWord step start
  refine ⟨by omega, ?_⟩
  refine le_trans hiter ?_
  have hmono : n * ((coeff.score WorkEvent.statement.units +
      coeff.score (WorkEvent.cost (whileOverhead + loopMoves fn)).units) +
      coeff.nativeCost * 98 + (bodyStoreBound coeff + bodyAssignBound coeff)) ≤
      b.toNat * ((coeff.score WorkEvent.statement.units +
      coeff.score (WorkEvent.cost (whileOverhead + loopMoves fn)).units) +
      coeff.nativeCost * 98 + (bodyStoreBound coeff + bodyAssignBound coeff)) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidate_capacity_init_cost_linear
