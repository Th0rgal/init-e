import Mathlib.Data.List.Permutation

namespace BoundedTableExperiment

open List

/-! ## Swap-remove order bookkeeping -/

/-- The exact order update of `htab_del`: replace position `i` by the last
entry and drop the last entry.  For the last position this is just `dropLast`. -/
def swapRemove : List α → Nat → List α
  | [], _ => []
  | [_], 0 => []
  | a :: as, 0 =>
      match as with
      | [] => []
      | b :: bs => (b :: bs).getLast (by simp) :: (b :: bs).dropLast
  | a :: as, i + 1 => a :: swapRemove as i

theorem perm_last_cons_dropLast {α : Type} (l : List α) (h : l ≠ []) :
    [l.getLast h] ++ l.dropLast ~ l := by
  have hcomm : [l.getLast h] ++ l.dropLast ~ l.dropLast ++ [l.getLast h] :=
    perm_append_comm
  simpa [dropLast_append_getLast h] using hcomm

/-- Swap-removal is a permutation of ordinary positional erasure. -/
theorem swapRemove_perm_eraseIdx {α : Type} (l : List α) (i : Nat)
    (hi : i < l.length) : swapRemove l i ~ l.eraseIdx i := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a as ih =>
      cases i with
      | zero =>
          cases as with
          | nil => simp [swapRemove, List.eraseIdx]
          | cons b bs =>
              simp [swapRemove, List.eraseIdx]
              exact perm_last_cons_dropLast (b :: bs) (by simp)
      | succ i =>
          simp only [swapRemove, List.eraseIdx, List.length_cons] at hi ⊢
          exact Perm.cons a (ih i (by omega))

/-! ## Leaf/internal pool ownership -/

/-- Every id in a pool segment lies in `1..cap`. -/
def Bounded (cap : Nat) (l : List Nat) : Prop :=
  ∀ x ∈ l, 1 ≤ x ∧ x ≤ cap

/-- Ownership of a leaf-id pool: two disjoint duplicate-free segments whose
lengths add to `cap`, and every id is in range.  Allocation moves an id from
`free` to `live`; deletion moves it back. -/
structure Owned (cap : Nat) (live free : List Nat) : Prop where
  liveNodup : live.Nodup
  freeNodup : free.Nodup
  disjoint : ∀ x, x ∈ live → x ∉ free
  lengthSum : live.length + free.length = cap
  liveBound : Bounded cap live
  freeBound : Bounded cap free

theorem Owned.alloc {cap : Nat} {live free : List Nat} (h : Owned cap live free)
    {x : Nat} (hx : x ∈ free) : Owned cap (live ++ [x]) (free.erase x) := by
  have hxnot : x ∉ live := fun hl => h.disjoint x hl hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h.liveNodup.append (by simp [hxnot])
  · exact h.freeNodup.erase x
  · intro y hy hyfree
    rw [List.mem_erase] at hyfree
    rcases hyfree with ⟨hyx, hyfree⟩
    rw [List.mem_append] at hy
    rcases hy with hy | hy
    · exact h.disjoint y hy hyfree
    · simp at hy
      exact hyx hy.symm ▸ hx
  · have hlen : (free.erase x).length + 1 = free.length := by
      rw [List.length_erase_of_mem hx]
      have : 0 < free.length := List.length_pos_of_mem hx
      omega
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · intro y hy
    rw [List.mem_append] at hy
    rcases hy with hy | hy
    · exact h.liveBound y hy
    · simp at hy
      subst hy
      exact h.freeBound x hx
  · intro y hy
    exact h.freeBound y (List.mem_of_mem_erase hy)

theorem Owned.free {cap : Nat} {live free : List Nat} (h : Owned cap live free)
    {x : Nat} (hx : x ∈ live) : Owned cap (live.erase x) (free ++ [x]) := by
  have hxnot : x ∉ free := h.disjoint x hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h.liveNodup.erase x
  · exact h.freeNodup.append (by simp [hxnot])
  · intro y hy hyfree
    rw [List.mem_append] at hyfree
    rcases hyfree with hyfree | hyfree
    · exact h.disjoint y (List.mem_of_mem_erase hy) hyfree
    · simp at hyfree
      subst hyfree
      exact (List.not_mem_erase x x) hy
  · have hlen : (live.erase x).length + 1 = live.length := by
      rw [List.length_erase_of_mem hx]
      have : 0 < live.length := List.length_pos_of_mem hx
      omega
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · intro y hy
    exact h.liveBound y (List.mem_of_mem_erase hy)
  · intro y hy
    rw [List.mem_append] at hy
    rcases hy with hy | hy
    · exact h.freeBound y hy
    · simp at hy
      subst hy
      exact h.liveBound x hx

/-! ## Reachable order invariant -/

/-- The order array lists exactly the live leaves, once each. -/
structure Ordered (order live : List Nat) : Prop where
  perm : order ~ live
  nodup : order.Nodup

theorem Ordered.insert {order live : List Nat} (h : Ordered order live) (x : Nat) :
    Ordered (order ++ [x]) (live ++ [x]) := by
  refine ⟨h.perm.append_right [x], ?_⟩
  exact h.nodup.append (by simp)
