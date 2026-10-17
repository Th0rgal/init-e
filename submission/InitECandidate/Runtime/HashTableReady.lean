import InitECandidate.Runtime.HashTableReady32
import InitECandidate.Runtime.HashTableArraysRead
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Live table facts parameterized by the actual key width. -/
structure HashTableLive {F : Type}
    (keyLength table keys stride capacity used values order orderPos count : BitVec 64)
    (bits : Nat) (pointer : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Prop where
  arrays : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state
  entries : HashOrderEntriesBound order capacity count state
  frontier : HashTableHeapFrontier32 orderPos capacity pointer state

/-- Reusable mixed-operation invariant for the actual source key width. -/
structure HashTableReady {F : Type}
    (keyLength table keys stride capacity used values order orderPos items : BitVec 64)
    (bits : Nat) (pointer : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Prop where
  live : HashTableLive keyLength table keys stride capacity used values order orderPos items bits pointer state
  valuesWord : HashValueEntriesWord used values capacity state
  reverse : HashReverseEntriesBound used orderPos capacity items state
  linked : HashOrderLinked used order orderPos capacity items state
  ordering : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat

 theorem HashTableReady.after_read {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos items : BitVec 64)
    (bits : Nat) (pointer : BitVec 64)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (memory : post.memory = state.memory) (globals : post.globals = state.globals)
    (code : post.code = state.code) (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be) :
    HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer post := by
  exact ⟨⟨ready.live.arrays.after_read state post keyLength table keys stride capacity used values order orderPos items bits memory code domain endian,
    ready.live.entries.after_memory state post order capacity items memory,
    ready.live.frontier.after_globals state post orderPos capacity pointer globals⟩,
    ready.valuesWord.after_read state post used values capacity memory domain endian,
    ready.reverse.after_read state post used orderPos capacity items memory domain endian,
    ready.linked.after_read state post used order orderPos capacity items memory domain endian,ready.ordering⟩


#print axioms HashTableReady.after_read
end InitECandidate.Runtime
