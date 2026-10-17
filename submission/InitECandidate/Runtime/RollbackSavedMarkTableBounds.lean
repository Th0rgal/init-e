import InitECandidate.Runtime.RollbackWorldAllocateKey
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Temporary scratch writes may change memory, but preserving the capacity
and reverse-array pointer of each table keeps live allocations below the saved mark. -/
theorem RollbackWorld.saved_mark_covers_tables {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {before after : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count before)
    (pointer : BitVec 64)
    (heap : before.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (headers : ∀ table ∈ tables, after.memory (table + 16) = before.memory (table + 16) ∧
      after.memory (table + 64) = before.memory (table + 64)) :
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
  rw [(headers table member).1] at capacityCell
  rw [(headers table member).2] at reverseCell
  have sameCapacity : oldCapacity = capacity := by
    simpa only [HolWordLab.word.injEq] using oldReady.live.arrays.cell16.symm.trans capacityCell
  have sameReverse : oldReverse = reverse := by
    simpa only [HolWordLab.word.injEq] using oldReady.live.arrays.cell64.symm.trans reverseCell
  have allocated := oldReady.live.frontier.allocated
  simpa only [sameCapacity,sameReverse,samePointer] using allocated

#print axioms RollbackWorld.saved_mark_covers_tables
end InitECandidate.Runtime
