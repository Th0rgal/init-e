import InitECandidate.Runtime.TransactionRegistryHeapBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Registered tables retain a common word-valued heap pointer even after
mutation calls relocate arrays or allocate saved journal keys. -/
theorem TransactionRegistryWorld.heap_exists {F : Type}
    {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {fieldPointer ts journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state) :
    ∃ pointer : BitVec 64, state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)) ∧
      pointer.toNat % 8 = 0 ∧ pointer.toNat ≤ 33806089496 ∧ ts.toNat + 72 ≤ pointer.toNat := by
  have binding : (8,fieldPointer) ∈ stateFreshTxTableBindings fieldPointer stateFreshTxAllTables := by
    simp [stateFreshTxAllTables,stateFreshTxTableBindings]
  have member := valid.fieldRegistry (stateFreshTx_binding_registered stateFreshTxAllTables fieldPointer ∅ (8,fieldPointer) binding)
  obtain ⟨pointer,keys,stride,capacity,used,values,order,reverse,items,bits,ready,_,_⟩ := valid.journalWorld.world.ready fieldPointer member
  have heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)) := ready.live.frontier.heap
  have facts := valid.heap_facts pointer heap
  exact ⟨pointer,heap,facts.1,valid.heap_bounded pointer heap,facts.2⟩

#print axioms TransactionRegistryWorld.heap_exists
end InitECandidate.Runtime
