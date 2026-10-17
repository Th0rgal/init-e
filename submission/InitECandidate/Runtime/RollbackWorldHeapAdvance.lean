import InitECandidate.Runtime.RollbackWorldFrame
import InitECandidate.Runtime.RollbackPhysicalSeparated
import InitECandidate.Runtime.HashTablePhysicalAdvanceFrame
import InitECandidate.Runtime.HeapGlobalsFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Allocator metadata changes preserve the whole world when memory is fixed
and the common heap frontier advances without wraparound. -/
theorem RollbackWorld.advance_heap {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {before after : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count before)
    (separated : RollbackPhysicalSeparated widths tables before)
    (pointer next : BitVec 64)
    (oldHeap : before.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (newHeap : after.globals.lookup (ofString "heap_ptr") = some (.val (.word next)))
    (advance : pointer.toNat ≤ next.toNat) (bounded : next.toNat ≤ 33806089496) (aligned : next.toNat % 8 = 0)
    (memory : after.memory = before.memory) (globals : HeapGlobalsFrame before after)
    (locals : after.locals = before.locals) (code : after.code = before.code)
    (domain : after.memaddrs = before.memaddrs) (endian : after.be = before.be) :
    RollbackWorld widths tables journal snapshot count after ∧ RollbackPhysicalSeparated widths tables after := by
  have retained : ∀ table ∈ tables, ∀ op keys stride capacity used values order reverse items bits,
      HashTableReady (widths table) table keys stride capacity used values order reverse items bits op before →
      HashTableReady (widths table) table keys stride capacity used values order reverse items bits next after := by
    intro table member op keys stride capacity used values order reverse items bits ready
    have same : op = pointer := by
      have equal := ready.live.frontier.heap.symm.trans oldHeap
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using equal
    subst op
    exact ready.physical_frame_advance before after (widths table) table pointer next keys stride capacity used values order reverse items bits
      (by intro address inside; exact congrFun memory address) newHeap advance bounded aligned code domain endian
  have family : ∀ table ∈ tables, RollbackTableReady widths table after := by
    intro table member
    obtain ⟨op,keys,stride,capacity,used,values,order,reverse,items,bits,ready,small,large⟩ := world.ready table member
    exact ⟨next,keys,stride,capacity,used,values,order,reverse,items,bits,
      retained table member op keys stride capacity used values order reverse items bits ready,small,large⟩
  have apart : RollbackPhysicalSeparated widths tables after := by
    apply separated.of_footprint_subset
    intro table member address inside
    obtain ⟨op,keys,stride,capacity,used,values,order,reverse,items,bits,ready,_,_⟩ := world.ready table member
    have updated := retained table member op keys stride capacity used values order reverse items bits ready
    exact (ready.rollback_footprint_iff before widths table op keys stride capacity used values order reverse items bits address).mpr
      ((updated.rollback_footprint_iff after widths table next keys stride capacity used values order reverse items bits address).mp inside)
  refine ⟨world.after_frame (Nat.le_refl _) ?_ ?_ ?_ domain ?_ family,apart⟩
  · exact (globals (ofString "journal_n") (by decide)).trans world.counter
  · rw [locals]; exact world.snapshotLocal
  · exact (globals (ofString "journal") (by decide)).trans world.journalGlobal
  · intro index inside offset member
    exact congrFun memory _

#print axioms RollbackWorld.advance_heap
end InitECandidate.Runtime
