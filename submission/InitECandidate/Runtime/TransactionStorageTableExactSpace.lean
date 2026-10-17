import InitECandidate.Runtime.TransactionStorageTableSafePlan
import InitECandidate.Runtime.AllocationPlanAligned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Exactly 528 free bytes suffice for the original storage constructor,
including the full transaction registry and its returned local assignment. -/
theorem TransactionRegistryWorld.new_storage_table_local_exact_space {F : Type}
    (state : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count pointer oldValue : BitVec 64) (name : MlS)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (localWord : state.locals.lookup name = some (.val (.word oldValue)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (space : pointer.toNat + 528 ≤ 33806089496) (ticks : 16 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state (.call (some (some (.local,name),none)) (ofString "htab_new") [.const 32,.const 8]) = (none,post) ∧
      TransactionRegistryWorld (withTableWidth widths pointer 32) (insert pointer tables) fieldPointer ts journal snapshot count post ∧
      state.clock ≤ post.clock + 16 ∧ post.clock ≤ state.clock ∧ post.locals.lookup name = some (.val (.word pointer)) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (htabNewOrderPos pointer 32 8) (8 * 8)))) := by
  have safe := (storageTable_safe_plan_iff pointer (valid.heap_bounded pointer heap) (valid.heap_facts pointer heap).1).mpr space
  exact valid.new_storage_table_local_of_safe_plan state widths tables fieldPointer ts journal snapshot count pointer oldValue name
    localWord heap safe ticks

#print axioms TransactionRegistryWorld.new_storage_table_local_exact_space
end InitECandidate.Runtime
