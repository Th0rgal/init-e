import InitECandidate.Runtime.RollbackAllocationCopySeparation
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every registered table header ends before the current heap frontier,
including after its arrays have been relocated. -/
theorem RollbackWorld.registered_header_before_frontier {F : Type}
    {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count state)
    (pointer table : BitVec 64) (member : table ∈ tables)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer))) :
    table.toNat + 72 ≤ pointer.toNat := by
  obtain ⟨oldPointer,keys,stride,capacity,used,values,order,reverse,items,bits,ready,_,_⟩ := world.ready table member
  have samePointer : oldPointer = pointer := by
    have equal := ready.live.frontier.heap.symm.trans heap
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using equal
  have := ready.live.arrays.headerKeys
  have := ready.live.arrays.keysBefore
  have := ready.live.arrays.usedBefore
  have := ready.live.arrays.orderBefore
  have := ready.live.frontier.allocated
  subst oldPointer
  omega

#print axioms RollbackWorld.registered_header_before_frontier
end InitECandidate.Runtime
