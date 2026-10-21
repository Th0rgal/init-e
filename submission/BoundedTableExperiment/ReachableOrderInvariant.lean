import Init

namespace BoundedTableExperiment

open List

theorem dropLast_append_getLast {α : Type} (l : List α) (h : l ≠ []) :
    l.dropLast ++ [l.getLast h] = l := by
  induction l with
  | nil => exact (h rfl).elim
  | cons a as ih =>
      cases as with
      | nil => simp
      | cons b bs =>
          have ih' := ih (by simp : (b :: bs) ≠ [])
          simp only [List.dropLast, List.getLast_cons (by simp : (b :: bs) ≠ [])]
          simpa using congrArg (fun t => a :: t) ih' 

theorem perm_last_cons_dropLast {α : Type} (l : List α) (h : l ≠ []) :
    [l.getLast h] ++ l.dropLast ~ l := by
  have hcomm : [l.getLast h] ++ l.dropLast ~ l.dropLast ++ [l.getLast h] :=
    List.perm_append_comm
  simpa [dropLast_append_getLast l h] using hcomm

/-- Exact swap-remove order update: replace position `i` by the last entry and
drop the last entry.  The final-position case removes the entry. -/
def swapRemove : List α → Nat → List α
  | [], _ => []
  | [_], 0 => []
  | a :: as, 0 =>
      match as with
      | [] => []
      | b :: bs => (b :: bs).getLast (by simp) :: (b :: bs).dropLast
  | a :: as, i + 1 => a :: swapRemove as i

/-- Swap-removal deletes exactly the key at the erased position, as a
permutation of ordinary list erasure. -/
theorem swapRemove_perm_erase {α : Type} [BEq α] [LawfulBEq α]
    (l : List α) (i : Nat) (x : α) (hi : i < l.length)
    (hx : l[i] = x) (hn : l.Nodup) : swapRemove l i ~ l.erase x := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a as ih =>
      cases i with
      | zero =>
          have hxa : x = a := by simpa using hx.symm
          subst x
          cases as with
          | nil => simp [swapRemove, List.erase_cons_head]
          | cons b bs =>
              simp only [swapRemove]
              simpa [List.erase_cons_head] using
                perm_last_cons_dropLast (b :: bs) (by simp)
      | succ i =>
          have hi' : i < as.length := by simpa using hi
          have hxas : as[i] = x := by
            rw [List.getElem_cons_succ a as i hi] at hx
            exact hx
          have hnot : a ∉ as := (List.nodup_cons.mp hn).1
          have hane : x ≠ a := by
            intro h
            have as_i_a : as[i] = a := by rw [hxas, h]
            have amem : a ∈ as := by
              rw [← as_i_a]
              exact List.getElem_mem hi'
            exact hnot amem
          have heq : ¬(a == x) = true := by
            simpa [beq_iff_eq] using fun h : a = x => hane h.symm
          simp only [swapRemove]
          rw [List.erase_cons_tail heq]
          exact List.Perm.cons a
            (ih i hi' hxas (List.nodup_cons.mp hn).2)

/-! ## Pool ownership -/

/-- The two pool segments are disjoint and together are a permutation of the
fixed pool.  Alloc/free move one id between the segments. -/
structure Owned {α : Type} [BEq α] [LawfulBEq α] (pool live free : List α) : Prop where
  partition : (live ++ free) ~ pool
  poolNodup : pool.Nodup

theorem Owned.alloc {α : Type} [BEq α] [LawfulBEq α] {pool live free : List α}
    (h : Owned pool live free) {x : α} (hx : x ∈ free) :
    Owned pool (live ++ [x]) (free.erase x) := by
  refine ⟨?_, h.poolNodup⟩
  calc
    (live ++ [x]) ++ free.erase x = live ++ (x :: free.erase x) := by simp
    _ ~ live ++ free := List.Perm.append_left live (List.perm_cons_erase hx).symm
    _ ~ pool := h.partition

theorem Owned.free {α : Type} [BEq α] [LawfulBEq α] {pool live free : List α}
    (h : Owned pool live free) {x : α} (hx : x ∈ live) :
    Owned pool (live.erase x) (free ++ [x]) := by
  refine ⟨?_, h.poolNodup⟩
  calc
    (live.erase x) ++ (free ++ [x]) = ((live.erase x) ++ free) ++ [x] := by simp
    _ ~ [x] ++ ((live.erase x) ++ free) := List.perm_append_comm
    _ ~ live ++ free := by
      exact List.Perm.append_right free (List.perm_cons_erase hx).symm
    _ ~ pool := h.partition

/-- The concrete leaf-id pool `1..cap`. -/
def leafPool (cap : Nat) : List Nat := (List.range cap).map (fun i => i + 1)

theorem leafPool_nodup (cap : Nat) : (leafPool cap).Nodup := by
  unfold leafPool
  apply List.Pairwise.map (R := fun a b : Nat => a ≠ b)
  · intro a b h
    omega
  · exact (show List.Pairwise (fun a b : Nat => a ≠ b) (List.range cap) from List.nodup_range)

theorem leafPool_length (cap : Nat) : (leafPool cap).length = cap := by
  simp [leafPool]

theorem leafPool_mem {cap x : Nat} : x ∈ leafPool cap ↔ 1 ≤ x ∧ x ≤ cap := by
  simp only [leafPool, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩
    omega
  · intro ⟨h1, h2⟩
    exact ⟨x - 1, by omega, by omega⟩

/-- Ownership specialized to the concrete id range `1..cap`. -/
abbrev CapOwned (cap : Nat) (live free : List Nat) : Prop :=
  Owned (leafPool cap) live free

theorem CapOwned.length {cap : Nat} {live free : List Nat}
    (h : CapOwned cap live free) : live.length + free.length = cap := by
  calc
    live.length + free.length = (live ++ free).length := by simp
    _ = (leafPool cap).length := h.partition.length_eq
    _ = cap := leafPool_length cap

theorem CapOwned.range_left {cap : Nat} {live free : List Nat}
    (h : CapOwned cap live free) {x : Nat} (hx : x ∈ live) : 1 ≤ x ∧ x ≤ cap := by
  apply leafPool_mem.mp
  exact h.partition.mem_iff.mp (List.mem_append.mpr (Or.inl hx))

theorem CapOwned.range_right {cap : Nat} {live free : List Nat}
    (h : CapOwned cap live free) {x : Nat} (hx : x ∈ free) : 1 ≤ x ∧ x ≤ cap := by
  apply leafPool_mem.mp
  exact h.partition.mem_iff.mp (List.mem_append.mpr (Or.inr hx))

/-- The order array is a permutation of the live leaves. -/
structure Ordered {α : Type} (order live : List α) : Prop where
  perm : order ~ live

theorem Ordered.insert {α : Type} {order live : List α} (h : Ordered order live)
    (x : α) : Ordered (order ++ [x]) (live ++ [x]) :=
  ⟨h.perm.append_right [x]⟩

/-- Deleting the entry at `order[i]` with swap-remove preserves the order
invariant, provided `order` has no duplicate entries. -/
theorem Ordered.delete {α : Type} [BEq α] [LawfulBEq α]
    {order live : List α} (h : Ordered order live) (i : Nat) (x : α)
    (hi : i < order.length) (hx : order[i] = x) (hn : order.Nodup) :
    Ordered (swapRemove order i) (live.erase x) :=
  ⟨(swapRemove_perm_erase order i x hi hx hn).trans (h.perm.erase x)⟩

end BoundedTableExperiment

#print axioms BoundedTableExperiment.swapRemove_perm_erase
#print axioms BoundedTableExperiment.Ordered.insert
#print axioms BoundedTableExperiment.CapOwned.length
#print axioms BoundedTableExperiment.CapOwned.range_left
#print axioms BoundedTableExperiment.Owned.alloc
#print axioms BoundedTableExperiment.Owned.free
#print axioms BoundedTableExperiment.Ordered.delete
