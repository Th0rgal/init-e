import InitECandidate.Runtime.SplitExtensionIncomingSource
import InitECandidate.Runtime.MptInsertBranchConstructorsBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem split_extension_single_child_bounded : ProgBounded splitExtensionSingleChild 0 :=
 ProgBounded.straight _ rfl

theorem split_extension_long_child_bounded : ProgBounded splitExtensionLongChild 3 := by
 unfold splitExtensionLongChild
 apply ProgBounded.ite
 · exact ProgBounded.decCall node_new_ext_fun_bounded _ _ _ (ProgBounded.straight _ rfl)
 · exact ProgBounded.weaken (cost:=0) (ProgBounded.straight _ rfl) (by omega)

theorem split_extension_leaf_child_bounded : ProgBounded splitExtensionLeafChildBody 3 := by
 unfold splitExtensionLeafChildBody
 exact ProgBounded.decCall node_new_leaf_fun_bounded _ _ _ (ProgBounded.straight _ rfl)

theorem split_extension_collision_guard_bounded : ProgBounded splitExtensionCollisionGuard 1 := by
 unfold splitExtensionCollisionGuard
 apply ProgBounded.ite
 · exact ProgBounded.call mpt_fail_fun_bounded _ _
 · exact ProgBounded.weaken (cost:=0) (ProgBounded.straight _ rfl) (by omega)

theorem split_extension_incoming_nonempty_bounded : ProgBounded splitExtensionIncomingNonempty 4 := by
 unfold splitExtensionIncomingNonempty
 apply ProgBounded.dec
 exact ProgBounded.seq split_extension_collision_guard_bounded split_extension_leaf_child_bounded

theorem split_extension_new_side_bounded : ProgBounded splitExtensionNewSide 4 := by
 rw [source_split_extension_incoming]
 apply ProgBounded.ite
 · exact ProgBounded.weaken (cost:=0) (ProgBounded.straight _ rfl) (by omega)
 · exact split_extension_incoming_nonempty_bounded

/-- Actual original tail after the new branch allocation and suffix binding.
The bound includes read/store/allocation failures and collision exceptions. -/
theorem split_extension_at5_bounded : ProgBounded (splitExtensionAt 5) 7 := by
 rw [source_split_extension_5,source_split_extension_6,source_split_extension_7,source_split_extension_8]
 exact ProgBounded.seq split_extension_single_child_bounded
  (ProgBounded.seq split_extension_long_child_bounded
   (ProgBounded.dec _ _ _ (ProgBounded.seq split_extension_new_side_bounded (ProgBounded.straight _ rfl))))

#print axioms split_extension_at5_bounded
#print axioms split_extension_new_side_bounded
end InitECandidate.Runtime
