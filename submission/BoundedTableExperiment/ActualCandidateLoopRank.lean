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
