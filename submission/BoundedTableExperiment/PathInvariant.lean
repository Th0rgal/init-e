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

end BoundedTableExperiment

#print axioms BoundedTableExperiment.splitIndex_prefix
#print axioms BoundedTableExperiment.splitIndex_suffix
#print axioms BoundedTableExperiment.strict_snoc
