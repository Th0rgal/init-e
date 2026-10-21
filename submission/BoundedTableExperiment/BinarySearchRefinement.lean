import Init

namespace BoundedTableExperiment

/-- The split specification: exactly the indices below `S` have route `<= d`. -/
def SplitSpec (routes : Nat → Nat) (d S : Nat) : Prop :=
  ∀ i, i < S ↔ routes i ≤ d

structure BS where
  lo : Nat
  hi : Nat

/-- One iteration of the PNK path binary search. -/
def step (routes : Nat → Nat) (d : Nat) (s : BS) : BS :=
  if h : s.lo < s.hi then
    let mid := (s.lo + s.hi) / 2
    if routes mid > d then ⟨s.lo, mid⟩ else ⟨mid + 1, s.hi⟩
  else s

theorem step_bounds (routes : Nat → Nat) (d : Nat) (s : BS)
    (h0 : s.lo ≤ s.hi) : (step routes d s).lo ≤ (step routes d s).hi := by
  by_cases h : s.lo < s.hi
  · simp only [step, h, dif_pos]
    split
    · change s.lo ≤ (s.lo + s.hi) / 2
      omega
    · change (s.lo + s.hi) / 2 + 1 ≤ s.hi
      omega
  · simp only [step, h, dif_neg, not_false_eq_true]
    exact h0

theorem step_split (routes : Nat → Nat) (d S : Nat) (s : BS)
    (hspec : SplitSpec routes d S) (hlo : s.lo ≤ S) (hhi : S ≤ s.hi) :
    (step routes d s).lo ≤ S ∧ S ≤ (step routes d s).hi := by
  by_cases h : s.lo < s.hi
  · simp only [step, h, dif_pos]
    split
    · have hnot : ¬ (s.lo + s.hi) / 2 < S := by
        intro hm
        have := (hspec ((s.lo + s.hi) / 2)).mp hm
        omega
      change s.lo ≤ S ∧ S ≤ (s.lo + s.hi) / 2
      exact ⟨hlo, by omega⟩
    · have hle : routes ((s.lo + s.hi) / 2) ≤ d := Nat.le_of_not_gt (by assumption)
      have hlt : (s.lo + s.hi) / 2 < S :=
        (hspec ((s.lo + s.hi) / 2)).mpr hle
      change (s.lo + s.hi) / 2 + 1 ≤ S ∧ S ≤ s.hi
      exact ⟨by omega, hhi⟩
  · simp only [step, h, dif_neg, not_false_eq_true]
    exact ⟨hlo, hhi⟩

theorem step_gap (routes : Nat → Nat) (d : Nat) (s : BS) (h : s.lo < s.hi) :
    (step routes d s).hi - (step routes d s).lo < s.hi - s.lo := by
  simp only [step, h, dif_pos]
  split
  · change (s.lo + s.hi) / 2 - s.lo < s.hi - s.lo
    omega
  · change s.hi - ((s.lo + s.hi) / 2 + 1) < s.hi - s.lo
    omega

/-- Fueled execution of the loop; one iteration per unit of fuel. -/
def run (routes : Nat → Nat) (d : Nat) : Nat → BS → BS
  | 0, s => s
  | n + 1, s => if s.lo < s.hi then run routes d n (step routes d s) else s

/-- The iterative binary search returns the unique split point. -/
theorem run_split (routes : Nat → Nat) (d S : Nat) (hspec : SplitSpec routes d S) :
    ∀ fuel s, s.lo ≤ S → S ≤ s.hi → s.hi - s.lo ≤ fuel →
      (run routes d fuel s).lo = S := by
  intro fuel
  induction fuel with
  | zero =>
      intro s hlo hhi hgap
      have : s.lo = s.hi := by omega
      have : s.lo = S := by omega
      simpa [run] using this
  | succ n ih =>
      intro s hlo hhi hgap
      by_cases h : s.lo < s.hi
      · have hbounds := step_split routes d S s hspec hlo hhi
        have hgap' : (step routes d s).hi - (step routes d s).lo ≤ n := by
          have := step_gap routes d s h
          omega
        simpa [run, h] using ih (step routes d s) hbounds.1 hbounds.2 hgap'
      · have : s.lo = s.hi := by omega
        have : s.lo = S := by omega
        simpa [run, h] using this

end BoundedTableExperiment

#print axioms BoundedTableExperiment.step_split
#print axioms BoundedTableExperiment.run_split
