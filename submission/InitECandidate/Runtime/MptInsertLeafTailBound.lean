import InitECandidate.Runtime.MptInsertLeafSource
import InitECandidate.Runtime.MptInsertBranchConstructorsBound
import InitECandidate.Runtime.CommonPrefixUniformBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The actual split suffix uses only the checked prefix comparison and
branch/extension constructors, with every failure outcome included. -/
theorem mpt_insert_leaf_split_tail_bounded : ProgBounded (mptInsertLeafAt 3) (2^64+100) := by
 have finish : ProgBounded (mptInsertLeafAt 5) 3 := by
  rw [source_mpt_insert_leaf_5]
  apply ProgBounded.seq (a:=3) (b:=0)
  · apply ProgBounded.ite
    · exact ProgBounded.tail node_new_ext_fun_bounded _
    · exact ProgBounded.weaken (cost:=0) (ProgBounded.straight _ rfl) (Nat.zero_le _)
  · exact ProgBounded.straight _ rfl
 have branch : ProgBounded (mptInsertLeafAt 4) 54 := by
  rw [source_mpt_insert_leaf_4]
  exact ProgBounded.decCall create_branch_two_leaves_fun_bounded _ _ _ finish
 have split : ProgBounded (mptInsertLeafAt 3) ((1+2^64)+1+54) := by
  rw [source_mpt_insert_leaf_3]
  exact ProgBounded.decCall common_prefix_fun_bounded _ _ _ branch
 intro F s code budget
 obtain ⟨spent,remaining,safe⟩:=split s code (by omega)
 exact ⟨by omega,remaining,safe⟩

#print axioms mpt_insert_leaf_split_tail_bounded
end InitECandidate.Runtime
