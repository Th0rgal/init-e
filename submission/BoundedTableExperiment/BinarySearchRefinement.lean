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

/-- Concrete word-addressed memory for the path buffer. -/
def Mem := Nat → Nat

def store (m : Mem) (a v : Nat) : Mem := fun x => if x = a then v else m x

def MemIn (a n x : Nat) : Prop := a ≤ x ∧ x < a + n

def MemDisjoint (a n b m : Nat) : Prop := a + n ≤ b ∨ b + m ≤ a

theorem mem_store_other (m : Mem) (a b v : Nat) (h : b ≠ a) :
    store m a v b = m b := by
  simp [store, h]

theorem mem_not_both (a n b m x : Nat) (h : MemDisjoint a n b m)
    (ha : MemIn a n x) (hb : MemIn b m x) : False := by
  unfold MemDisjoint MemIn at *
  omega

/-- The abstract path slot `i` is the concrete load at `base + i*8`. -/
def pathAt (m : Mem) (base i : Nat) : Nat := m (base + i * 8)

/-- The abstract path list of length `n` built from concrete loads. -/
def pathList (m : Mem) (base n : Nat) : List Nat :=
  (List.range n).map (pathAt m base)

theorem pathList_getD (m : Mem) (base n i : Nat) (h : i < n) :
    (pathList m base n).getD i 0 = pathAt m base i := by
  rw [List.getD_eq_getElem?_getD, pathList, List.getElem?_map,
    List.getElem?_range h]
  rfl

theorem pathList_succ (m : Mem) (base n : Nat) :
    pathList m base (n + 1) = pathList m base n ++ [pathAt m base n] := by
  simp [pathList, List.range_succ, List.map_append]

/-- A path store lies inside the path region. -/
theorem path_store_in (base size depth : Nat) (hsize : (depth + 1) * 8 ≤ size) :
    MemIn base size (base + depth * 8) := by
  unfold MemIn; omega

/-- A path store cannot touch another disjoint region. -/
theorem path_store_not_other (pbase psize obase osize depth a : Nat)
    (hdisj : MemDisjoint pbase psize obase osize)
    (hpsize : (depth + 1) * 8 ≤ psize) (ha : MemIn obase osize a) :
    a ≠ pbase + depth * 8 := by
  intro heq
  rw [heq] at ha
  exact mem_not_both pbase psize obase osize (pbase + depth * 8) hdisj
    (path_store_in pbase psize depth hpsize) ha

/-- After a path store, a load in any disjoint region is unchanged. -/
theorem path_store_other_load (m : Mem) (pbase psize obase osize depth a v : Nat)
    (hdisj : MemDisjoint pbase psize obase osize)
    (hpsize : (depth + 1) * 8 ≤ psize) (ha : MemIn obase osize a) :
    store m (pbase + depth * 8) v a = m a := by
  exact mem_store_other m _ a v (path_store_not_other pbase psize obase osize depth a hdisj hpsize ha)

/-- A path store at `depth` does not change an earlier slot `i`. -/
theorem path_store_old_slot (m : Mem) (base depth i v : Nat) (h : i ≠ depth) :
    pathAt (store m (base + depth * 8) v) base i = pathAt m base i := by
  unfold pathAt
  apply mem_store_other
  intro heq
  apply h
  omega

/-- The stored slot reads back the stored value. -/
theorem path_store_new_slot (m : Mem) (base depth v : Nat) :
    pathAt (store m (base + depth * 8) v) base depth = v := by
  unfold pathAt
  simp [store]

/-- Binary-search refinement instantiated with concrete path-memory loads. -/
theorem run_split_path (m : Mem) (base d S : Nat)
    (hspec : SplitSpec (pathAt m base) d S) :
    ∀ fuel s, s.lo ≤ S → S ≤ s.hi → s.hi - s.lo ≤ fuel →
      (run (pathAt m base) d fuel s).lo = S :=
  run_split (pathAt m base) d S hspec

/-- Every binary-search read is the load at a concrete path address. -/
theorem path_read_is_load (m : Mem) (base mid : Nat) :
    pathAt m base mid = m (base + mid * 8) := rfl

end BoundedTableExperiment

#print axioms BoundedTableExperiment.step_split
#print axioms BoundedTableExperiment.run_split
#print axioms BoundedTableExperiment.path_store_other_load
#print axioms BoundedTableExperiment.pathList_getD
#print axioms BoundedTableExperiment.run_split_path
