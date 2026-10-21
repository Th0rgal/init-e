import Init

namespace BoundedTableExperiment

/-- A lookup skips a prefix whose entries do not mention the key. -/
theorem lookup_skip_prefix_generic {A B : Type} [BEq A]
    (before suffix : List (A × B)) (key : A)
    (absent : before.all (fun entry => !(key == entry.1)) = true) :
    List.lookup key (before ++ suffix) = List.lookup key suffix := by
  induction before with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk name value =>
        simp only [List.all_cons, Bool.and_eq_true] at absent
        rcases absent with ⟨hhead, htail⟩
        by_cases hkey : key == name
        · rw [hkey] at hhead
          exact absurd hhead (by simp)
        · have hne : (key == name) = false := by simpa using hkey
          rw [List.cons_append, List.lookup_cons]
          simp only [hne, Bool.false_eq_true, if_false]
          exact ih htail

end BoundedTableExperiment

#print axioms BoundedTableExperiment.lookup_skip_prefix_generic
