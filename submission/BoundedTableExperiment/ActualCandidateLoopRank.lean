import ActualCandidateLoopBodyBound

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
