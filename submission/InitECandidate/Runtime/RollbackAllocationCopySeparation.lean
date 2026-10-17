import InitECandidate.Runtime.RollbackWorldAllocateKey
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Allocation leaves table header identities unchanged, so every possible
ready-table witness after allocation still ends before the old frontier. -/
theorem RollbackWorld.copy_separation_after_memory {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {before after : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count before)
    (pointer : BitVec 64)
    (heap : before.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (memory : after.memory = before.memory) :
    ∀ table ∈ tables, ∀ op keys stride capacity used values order reverse items bits,
      HashTableReady (widths table) table keys stride capacity used values order reverse items bits op after →
      reverse.toNat + capacity.toNat * 8 ≤ pointer.toNat := by
  intro table member op keys stride capacity used values order reverse items bits ready
  obtain ⟨oldPointer,oldKeys,oldStride,oldCapacity,oldUsed,oldValues,oldOrder,oldReverse,oldItems,oldBits,oldReady,_,_⟩ := world.ready table member
  have samePointer : oldPointer = pointer := by
    have equal := oldReady.live.frontier.heap.symm.trans heap
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using equal
  have capacityCell := ready.live.arrays.cell16
  have reverseCell := ready.live.arrays.cell64
  rw [memory] at capacityCell reverseCell
  have sameCapacity : oldCapacity = capacity := by
    simpa only [HolWordLab.word.injEq] using oldReady.live.arrays.cell16.symm.trans capacityCell
  have sameReverse : oldReverse = reverse := by
    simpa only [HolWordLab.word.injEq] using oldReady.live.arrays.cell64.symm.trans reverseCell
  have allocated := oldReady.live.frontier.allocated
  simpa only [sameCapacity,sameReverse,samePointer] using allocated

/-- Any live registered table places the live journal prefix below the common
heap frontier; no separate journal/copy separation premise is needed. -/
theorem RollbackWorld.journal_before_frontier {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count state)
    (pointer witness : BitVec 64) (member : witness ∈ tables)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer))) :
    journal.toNat + count.toNat * 32 ≤ pointer.toNat := by
  obtain ⟨oldPointer,keys,stride,capacity,used,values,order,reverse,items,bits,ready,_,_⟩ := world.ready witness member
  have samePointer : oldPointer = pointer := by
    have equal := ready.live.frontier.heap.symm.trans heap
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using equal
  have := world.layout witness member
  have := ready.live.arrays.headerKeys
  have := ready.live.arrays.keysBefore
  have := ready.live.arrays.usedBefore
  have := ready.live.arrays.orderBefore
  have := ready.live.frontier.allocated
  subst oldPointer
  omega

#print axioms RollbackWorld.copy_separation_after_memory
#print axioms RollbackWorld.journal_before_frontier
end InitECandidate.Runtime
