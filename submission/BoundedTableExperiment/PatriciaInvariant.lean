import Init

namespace BoundedTableExperiment

/-- A binary Patricia shape.  `bit` is the branching bit position. -/
inductive Tree where
  | leaf
  | branch (bit : Nat) (left right : Tree)
  deriving DecidableEq

namespace Tree

def leaves : Tree → Nat
  | leaf => 1
  | branch _ l r => leaves l + leaves r

def nodes : Tree → Nat
  | leaf => 1
  | branch _ l r => 1 + nodes l + nodes r

def depth : Tree → Nat
  | leaf => 1
  | branch _ l r => 1 + max (depth l) (depth r)

/-- All branch bits are strictly between `lo` and `hi`. -/
def Between (lo hi : Nat) : Tree → Prop
  | leaf => True
  | branch b l r => lo < b ∧ b < hi ∧ Between lo b l ∧ Between b hi r

theorem leaves_pos (t : Tree) : 0 < leaves t := by
  induction t with
  | leaf => simp [leaves]
  | branch b l r ihl ihr => simp [leaves]; omega

/-- A full binary tree with `L` leaves has exactly `2L-1` nodes. -/
theorem nodes_eq (t : Tree) : nodes t = 2 * leaves t - 1 := by
  induction t with
  | leaf => simp [nodes, leaves]
  | branch b l r ihl ihr =>
      have hl := leaves_pos l
      have hr := leaves_pos r
      simp [nodes, leaves, ihl, ihr]
      omega

/-- The Patricia pool bound: at most two nodes per live key. -/
theorem nodes_le_two_leaves (t : Tree) : nodes t ≤ 2 * leaves t := by
  have h := nodes_eq t
  have hp := leaves_pos t
  omega

/-- A strictly increasing bit range bounds every root-to-leaf path. -/
theorem depth_le_span : ∀ {lo hi : Nat} {t : Tree}, Between lo hi t → lo < hi →
    depth t ≤ hi - lo := by
  intro lo hi t
  revert lo hi
  induction t with
  | leaf =>
      intro lo hi h hpos
      simp [depth]
      omega
  | branch b l r ihl ihr =>
      intro lo hi h hpos
      obtain ⟨hlob, hbhi, hleft, hright⟩ := h
      have idl : depth l ≤ b - lo := ihl hleft hlob
      have idr : depth r ≤ hi - b := ihr hright hbhi
      have hmax : max (depth l) (depth r) ≤ max (b - lo) (hi - b) := by
        exact Nat.max_le.mpr
          ⟨Nat.le_trans idl (Nat.le_max_left _ _),
           Nat.le_trans idr (Nat.le_max_right _ _)⟩
      have hspan : max (b - lo) (hi - b) + 1 ≤ hi - lo := by omega
      simp [depth]
      omega

/-- With `B` key bits, lookup visits at most `B` internal nodes and one leaf. -/
theorem depth_le_key_bits {B : Nat} {t : Tree} (h : Between 0 B t) (hB : 0 < B) :
    depth t ≤ B := by
  have := depth_le_span h hB
  simpa using this

end Tree

end BoundedTableExperiment

#print axioms BoundedTableExperiment.Tree.nodes_eq
#print axioms BoundedTableExperiment.Tree.nodes_le_two_leaves
#print axioms BoundedTableExperiment.Tree.depth_le_key_bits
