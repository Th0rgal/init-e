import InitECandidate.Runtime.TransactionRegistryWidths
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The first transaction field supplies a registered witness, so the current
heap frontier is aligned and lies beyond the transaction header. -/
theorem TransactionRegistryWorld.heap_facts {F : Type}
    {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {fieldPointer ts journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (pointer : BitVec 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer))) :
    pointer.toNat % 8 = 0 ∧ ts.toNat + 72 ≤ pointer.toNat := by
  have binding : (8,fieldPointer) ∈ stateFreshTxTableBindings fieldPointer stateFreshTxAllTables := by
    simp [stateFreshTxAllTables,stateFreshTxTableBindings]
  have member := valid.fieldRegistry (stateFreshTx_binding_registered stateFreshTxAllTables fieldPointer ∅ (8,fieldPointer) binding)
  obtain ⟨oldPointer,keys,stride,capacity,used,values,order,reverse,items,bits,ready,_,_⟩ := valid.journalWorld.world.ready fieldPointer member
  have same : oldPointer = pointer := by
    have equal := ready.live.frontier.heap.symm.trans heap
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using equal
  have aligned := ready.live.frontier.aligned
  rw [same] at aligned
  have header := valid.tableHeaders fieldPointer member
  have frontier := valid.journalWorld.world.registered_header_before_frontier pointer fieldPointer member heap
  exact ⟨aligned,by omega⟩

#print axioms TransactionRegistryWorld.heap_facts
end InitECandidate.Runtime
