import InitECandidate.Runtime.TransactionRegistryHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A registered table witnesses the upper bound on the common heap frontier. -/
theorem TransactionRegistryWorld.heap_bounded {F : Type}
    {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {fieldPointer ts journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (pointer : BitVec 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer))) :
    pointer.toNat ≤ 33806089496 := by
  have binding : (8,fieldPointer) ∈ stateFreshTxTableBindings fieldPointer stateFreshTxAllTables := by
    simp [stateFreshTxAllTables,stateFreshTxTableBindings]
  have member := valid.fieldRegistry (stateFreshTx_binding_registered stateFreshTxAllTables fieldPointer ∅ (8,fieldPointer) binding)
  obtain ⟨oldPointer,keys,stride,capacity,used,values,order,reverse,items,bits,ready,_,_⟩ := valid.journalWorld.world.ready fieldPointer member
  have same : oldPointer = pointer := by
    have equal := ready.live.frontier.heap.symm.trans heap
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using equal
  simpa only [same] using ready.live.frontier.bounded

#print axioms TransactionRegistryWorld.heap_bounded
end InitECandidate.Runtime
