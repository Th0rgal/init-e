import InitECandidate.Runtime.RollbackWorldRead
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Only the heap pointer among globals is needed by a ready table. -/
theorem HashTableReady.after_heap_read {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (memory : post.memory = state.memory)
    (heap : post.globals.lookup (ofString "heap_ptr") = state.globals.lookup (ofString "heap_ptr"))
    (code : post.code = state.code) (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be) :
    HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer post := by
  exact ⟨⟨ready.live.arrays.after_read state post keyLength table keys stride capacity used values order orderPos items bits memory code domain endian,
    ready.live.entries.after_memory state post order capacity items memory,
    ⟨heap.trans ready.live.frontier.heap,ready.live.frontier.allocated,ready.live.frontier.bounded,ready.live.frontier.aligned⟩⟩,
    ready.valuesWord.after_read state post used values capacity memory domain endian,
    ready.reverse.after_read state post used orderPos capacity items memory domain endian,
    ready.linked.after_read state post used order orderPos capacity items memory domain endian,ready.ordering⟩

theorem RollbackPhysicalSeparated.after_heap_read {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {before after : PanSemStateFiniteExact 64 F}
    (separated : RollbackPhysicalSeparated widths tables before)
    (memory : after.memory = before.memory)
    (heap : after.globals.lookup (ofString "heap_ptr") = before.globals.lookup (ofString "heap_ptr"))
    (code : after.code = before.code) (domain : after.memaddrs = before.memaddrs) (endian : after.be = before.be) :
    RollbackPhysicalSeparated widths tables after := by
  apply separated.of_footprint_subset
  intro table member address inside
  obtain ⟨pointer,keys,stride,capacity,used,values,order,orderPos,items,bits,ready,region⟩ := inside
  exact ⟨pointer,keys,stride,capacity,used,values,order,orderPos,items,bits,
    ready.after_heap_read after before (widths table) table pointer keys stride capacity used values order orderPos items bits
      memory.symm heap.symm code.symm domain.symm endian.symm,region⟩

theorem RollbackPhysicalSeparated.after_global {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {state : PanSemStateFiniteExact 64 F} (separated : RollbackPhysicalSeparated widths tables state)
    (name : MlS) (value : ValueHOL 64) (different : name ≠ ofString "heap_ptr") :
    RollbackPhysicalSeparated widths tables (setGlobalHOLFinite name value state) := by
  apply separated.after_heap_read (after := setGlobalHOLFinite name value state) rfl ?_ rfl rfl rfl
  simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different]

#print axioms HashTableReady.after_heap_read
#print axioms RollbackPhysicalSeparated.after_heap_read
#print axioms RollbackPhysicalSeparated.after_global
end InitECandidate.Runtime
