import InitECandidate.Runtime.HashTableReady32
import InitECandidate.Runtime.HashTableArraysHeaderFrame32
import InitECandidate.Runtime.HashOrderLinkedInsert
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Local frames retain the reusable table state across unrelated heap writes. -/
theorem HashTableReady32.framed {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (header : ∀ offset ∈ ([0,8,16,24,32,40,48,56,64] : List Nat),
      post.memory (table + BitVec.ofNat 64 offset) = state.memory (table + BitVec.ofNat 64 offset))
    (occupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      hashOccupancyRead post used slot = hashOccupancyRead state used slot)
    (valueFrame : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      post.memory (values + slot * 8) = state.memory (values + slot * 8))
    (reverseFrame : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      post.memory (orderPos + slot * 8) = state.memory (orderPos + slot * 8))
    (orderFrame : ∀ position : BitVec 64, position.toNat < items.toNat →
      post.memory (order + position * 8) = state.memory (order + position * 8))
    (globals : post.globals = state.globals) (code : post.code = state.code)
    (domain : post.memaddrs = state.memaddrs) :
    HashTableReady32 table keys stride capacity used values order orderPos items bits pointer post := by
  have before : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      hashOccupancyRead post used slot ≠ some 0 → hashOccupancyRead state used slot ≠ some 0 := by
    intro slot inside occupied
    rw [← occupancy slot inside]
    exact occupied
  have ordered : HashOrderEntriesBound order capacity items post := by
    intro position inside
    obtain ⟨slot,cell,bound⟩ := ready.live.entries position inside
    exact ⟨slot,(orderFrame position inside).trans cell,bound⟩
  have words : HashValueEntriesWord used values capacity post := by
    intro slot inside occupied
    obtain ⟨value,cell⟩ := ready.valuesWord slot inside (before slot inside occupied)
    exact ⟨value,(valueFrame slot inside).trans cell⟩
  have reverse : HashReverseEntriesBound used orderPos capacity items post := by
    intro slot inside occupied
    obtain ⟨position,cell,bound⟩ := ready.reverse slot inside (before slot inside occupied)
    exact ⟨position,(reverseFrame slot inside).trans cell,bound⟩
  exact ⟨⟨ready.live.arrays.framed state post table keys stride capacity used values order orderPos items bits
      header occupancy code domain,ordered,ready.live.frontier.after_globals state post orderPos capacity pointer globals⟩,
    words,reverse,ready.linked.framed state post used order orderPos capacity items before reverseFrame orderFrame,ready.ordering⟩

#print axioms HashTableReady32.framed
end InitECandidate.Runtime
