import Init

namespace BoundedTableExperiment

open List

def Strict (l : List Nat) : Prop := l.Pairwise (fun a b => a < b)

def splitIndex : List Nat → Nat → Nat
  | [], _ => 0
  | a :: as, d => if a ≤ d then 1 + splitIndex as d else 0

theorem splitIndex_le_length (l : List Nat) (d : Nat) :
    splitIndex l d ≤ l.length := by
  induction l with
  | nil => simp [splitIndex]
  | cons a as ih =>
      by_cases h : a ≤ d
      · simp [splitIndex, h]; omega
      · simp [splitIndex, h]

theorem splitIndex_prefix (l : List Nat) (d : Nat) :
    ∀ r ∈ l.take (splitIndex l d), r ≤ d := by
  induction l with
  | nil => simp [splitIndex]
  | cons a as ih =>
      by_cases h : a ≤ d
      · have hs : splitIndex (a :: as) d = 1 + splitIndex as d := by
          simp [splitIndex, h]
        rw [hs]
        rw [Nat.add_comm 1 (splitIndex as d)]
        rw [List.take_succ_cons]
        intro r hr
        rw [List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact h
        · exact ih r hr
      · have hs : splitIndex (a :: as) d = 0 := by simp [splitIndex, h]
        rw [hs]
        simp

theorem splitIndex_suffix (l : List Nat) (d : Nat) (hmono : Strict l) :
    ∀ r ∈ l.drop (splitIndex l d), d < r := by
  induction l with
  | nil => simp [splitIndex]
  | cons a as ih =>
      have hmono' : List.Pairwise (fun a b => a < b) (a :: as) := hmono
      have htail : Strict as := (List.pairwise_cons.mp hmono').2
      by_cases h : a ≤ d
      · have hs : splitIndex (a :: as) d = 1 + splitIndex as d := by
          simp [splitIndex, h]
        rw [hs]
        rw [Nat.add_comm 1 (splitIndex as d)]
        rw [List.drop_succ_cons]
        exact ih htail
      · have hs : splitIndex (a :: as) d = 0 := by simp [splitIndex, h]
        rw [hs]
        simp only [List.drop_zero]
        intro r hr
        rw [List.mem_cons] at hr
        rcases hr with rfl | hr
        · omega
        · have ha : a < r := (List.pairwise_cons.mp hmono').1 r hr
          omega

theorem strict_snoc {l : List Nat} {r : Nat} (h : Strict l)
    (hall : ∀ x ∈ l, x < r) : Strict (l ++ [r]) := by
  change List.Pairwise (fun a b => a < b) (l ++ [r])
  rw [List.pairwise_append]
  refine ⟨h, by simp, ?_⟩
  intro a ha b hb
  simp at hb
  subst hb
  exact hall a ha


#print axioms BoundedTableExperiment.splitIndex_prefix
#print axioms BoundedTableExperiment.splitIndex_suffix
#print axioms BoundedTableExperiment.strict_snoc

/-- A route strictly after the split is greater than `d`. -/
theorem splitIndex_eq_of_take_drop (l : List Nat) (d i : Nat) (hmono : Strict l)
    (hi : i ≤ l.length)
    (hpre : ∀ r ∈ l.take i, r ≤ d)
    (hsuf : ∀ r ∈ l.drop i, d < r) : splitIndex l d = i := by
  induction l generalizing i with
  | nil =>
      have : i = 0 := by simp at hi; omega
      subst this
      simp [splitIndex]
  | cons a as ih =>
      cases i with
      | zero =>
          cases as with
          | nil =>
              have hlt : d < a := hsuf a (by simp)
              simp [splitIndex, Nat.not_le.mpr hlt]
          | cons b bs =>
              have hmem : a ∈ (a :: b :: bs).drop 0 := by simp
              have : d < a := hsuf a hmem
              simp [splitIndex, Nat.not_le.mpr (by omega)]
      | succ i =>
          have ha : a ≤ d := hpre a (by simp)
          have htail : Strict as := (List.pairwise_cons.mp hmono).2
          have hi' : i ≤ as.length := by simpa using hi
          have hpre' : ∀ r ∈ as.take i, r ≤ d := by
            intro r hr
            exact hpre r (by simp [hr])
          have hsuf' : ∀ r ∈ as.drop i, d < r := by
            intro r hr
            exact hsuf r (by simp [hr])
          simp only [splitIndex, ha, if_true]
          have := ih i htail hi' hpre' hsuf'
          omega

def bsearchList (l : List Nat) (d : Nat) : Nat :=
  let rec go : Nat → List Nat → Nat
    | 0, _ => 0
    | _ + 1, [] => 0
    | n + 1, l =>
        let mid := l.length / 2
        if l.getD mid 0 > d then go n (l.take mid)
        else mid + 1 + go n (l.drop (mid + 1))
  go (l.length + 1) l

#eval bsearchList [1, 3, 7, 9] 5
#eval splitIndex [1, 3, 7, 9] 5
#eval bsearchList [1, 3, 7, 9] 0
#eval splitIndex [1, 3, 7, 9] 0
#eval bsearchList (List.range 64 |>.map (· * 2)) 77
#eval splitIndex (List.range 64 |>.map (· * 2)) 77

#print axioms splitIndex_eq_of_take_drop

end BoundedTableExperiment
