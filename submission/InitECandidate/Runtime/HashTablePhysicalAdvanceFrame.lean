import InitECandidate.Runtime.HashTablePhysicalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A framed table survives other heap work, including allocations and global
updates, whenever the common frontier advances within the original heap. -/
theorem HashTableReady.physical_frame_advance {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (keyLength table pointer next keys stride capacity used values order orderPos items : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (frame : ∀ address : BitVec 64, tablePhysicalRegion table keys stride capacity used values order orderPos address → post.memory address = state.memory address)
    (heap : post.globals.lookup (ofString "heap_ptr") = some (.val (.word next)))
    (monotone : pointer.toNat ≤ next.toNat) (bounded : next.toNat ≤ 33806089496) (aligned : next.toNat % 8 = 0)
    (code : post.code = state.code) (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be) :
    HashTableReady keyLength table keys stride capacity used values order orderPos items bits next post := by
  let framed := {post with globals := state.globals}
  have retained := ready.physical_frame state framed keyLength table pointer keys stride capacity used values order orderPos items bits
    frame rfl code domain endian
  exact ⟨⟨retained.live.arrays.after_read framed post keyLength table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl,
    retained.live.entries.after_memory framed post order capacity items rfl,
    ready.live.frontier.advance state post orderPos capacity pointer next heap monotone bounded aligned⟩,
    retained.valuesWord.after_read framed post used values capacity rfl rfl rfl,
    retained.reverse.after_read framed post used orderPos capacity items rfl rfl rfl,
    retained.linked.after_read framed post used order orderPos capacity items rfl rfl rfl,ready.ordering⟩

/-- Every live region is below the common heap frontier, even after relocation. -/
theorem HashTableReady.physical_below_frontier {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (address : BitVec 64) (member : tablePhysicalRegion table keys stride capacity used values order orderPos address) :
    address.toNat < pointer.toNat := by
  have hk := ready.live.arrays.headerKeys
  have ku := ready.live.arrays.keysBefore
  have vu := ready.live.arrays.valuesBefore
  have uo := ready.live.arrays.usedBefore
  have oo := ready.live.arrays.orderBefore
  have allocated := ready.live.frontier.allocated
  unfold tablePhysicalRegion at member
  omega

#print axioms HashTableReady.physical_below_frontier
#print axioms HashTableReady.physical_frame_advance
end InitECandidate.Runtime
